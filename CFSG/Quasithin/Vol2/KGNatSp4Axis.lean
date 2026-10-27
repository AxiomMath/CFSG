module

public import CFSG.Quasithin.Vol2.KGNatSp4Sim
public import CFSG.Quasithin.Vol2.KGNatPointT
public import CFSG.Quasithin.Vol2.KGNatSemiLin
public import CFSG.Quasithin.Vol2.Ch11SecHFacts

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)

theorem exists_isometry_of_invol {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type*}
    [CommGroup W] {H : Subgroup (MulAut W)} {π : ↥(StatedSp 2 K) →* ↥H}
    {f : W → (Fin 2 ⊕ Fin 2 → K)} (hf : IsCoord (linModelNat (StatedSp 2 K)) H ⊥ π f)
    {x : MulAut W} (hxN : x ∈ Subgroup.normalizer (H : Set (MulAut W))) (hxx : x * x = 1)
    (hcard : Nat.card W < Nat.card {w : W // x w = w} ^ 2) :
    ∃ L : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K), (∀ w, L (f w) = f (x w)) ∧
      ∀ u v, Matrix.toBilin' (spJ K) (L u) (L v) = Matrix.toBilin' (spJ K) u v := by
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  have hx' : ∀ h ∈ H, x⁻¹ * h * x ∈ H := fun h hh => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) h).mp hh
    rwa [inv_inv] at this
  have he0 : (Pi.single (.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
    (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun h (.inl 0))
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSp T hT) he0 x
    (bot_maps x) (bot_maps x⁻¹) hx'
  set T := hf.autMap x (bot_maps x) with hTdef
  have hTf : ∀ w, T (f w) = f (x w) := hf.autMap_apply x (bot_maps x)
  have hfix : Nat.card (fixAdd T) = Nat.card {w : W // x w = w} := by
    refine (Nat.card_congr (Equiv.ofBijective (fun w : {w : W // x w = w} =>
      (⟨f w, ?_⟩ : fixAdd T)) ⟨?_, ?_⟩)).symm
    · rw [mem_fixAdd, hTf, w.2]
    · intro a b hab
      exact Subtype.ext (hinj _ _ (congrArg Subtype.val hab))
    · rintro ⟨v, hv⟩
      obtain ⟨w, rfl⟩ := hf.surj v
      exact ⟨⟨w, hinj _ _ ((hTf w).symm.trans hv)⟩, rfl⟩
  have hWM : Nat.card W = Nat.card (Fin 2 ⊕ Fin 2 → K) :=
    Nat.card_congr (Equiv.ofBijective f ⟨fun a b h => hinj a b h, hf.surj⟩)
  have hσid : ∀ c, σ c = c := semilinear_eq_id_of_card_fix hσ (by rw [hfix, ← hWM]; exact hcard)
  let TL : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := T
      map_add' := map_add T
      map_smul' := fun c v => by rw [hσ, hσid]; rfl }
  have hTL : ∀ w, TL (f w) = f (x w) := hTf
  have hnorm : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ v,
      TL (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        ((γ' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ TL v := by
    intro γ
    have hmem : x * ((π γ : ↥H) : MulAut W) * x⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp hxN _).mp (π γ).2
    obtain ⟨γ', hγ'⟩ := hf.onto ⟨_, hmem⟩
    refine ⟨γ', fun v => ?_⟩
    have h1 := hf.autMap_lin x (bot_maps x) γ' γ (congrArg Subtype.val hγ').symm v
    exact (congrArg T (linModelNat_lin _ γ v).symm).trans (h1.trans (linModelNat_lin _ γ' _))
  obtain ⟨c, hc⟩ := exists_similitude TL hnorm
  have hTT : ∀ v, TL (TL v) = v := by
    intro v
    obtain ⟨w, rfl⟩ := hf.surj v
    rw [hTL, hTL, ← MulAut.mul_apply, hxx, MulAut.one_apply]
  have hc1 : c = 1 := similitude_eq_one hTT hc
  refine ⟨TL, hTL, fun u v => ?_⟩
  rw [hc, hc1, one_mul]

theorem factAxisGroupSp4_holds : Ch11.SecH.FactAxisGroupSp4 := by
  intro F _ _ n hn hF W _ _ hW H π hπ E U hEN hEinv hEU hcard
  have : CharP F 2 := charP_two_of_card (by omega) hF
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have hinj : Function.Injective f := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  have hW4 : Nat.card W = Nat.card F ^ 4 := by
    rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hf.surj⟩), Nat.card_fun]
    simp
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hU3 : Nat.card F ^ 3 ≤ Nat.card U := by
    have h1 : Nat.card F ^ 4 ≤ Nat.card F * Nat.card U := by rw [← hW4, hF]; exact hcard
    rw [pow_succ'] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have hfixcard : ∀ x ∈ E, Nat.card W < Nat.card {w : W // x w = w} ^ 2 := by
    intro x hx
    have h1 : Nat.card U ≤ Nat.card {w : W // x w = w} :=
      Nat.card_le_card_of_injective (fun u : U => ⟨u, hEU x hx u u.2⟩)
        fun a b h => Subtype.ext (congrArg (fun z : {w : W // x w = w} => (z : W)) h)
    calc Nat.card W = Nat.card F ^ 4 := hW4
      _ < Nat.card F ^ 6 := Nat.pow_lt_pow_right hq (by norm_num)
      _ = (Nat.card F ^ 3) ^ 2 := by ring
      _ ≤ Nat.card {w : W // x w = w} ^ 2 := Nat.pow_le_pow_left (hU3.trans h1) 2
  have hL : ∀ x : ↥E, ∃ L : (Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 2 ⊕ Fin 2 → F),
      (∀ w, L (f w) = f ((x : MulAut W) w)) ∧
        ∀ u v, Matrix.toBilin' (spJ F) (L u) (L v) = Matrix.toBilin' (spJ F) u v := fun x =>
    exists_isometry_of_invol hf (hEN x.2) (hEinv x x.2) (hfixcard x x.2)
  choose L hLf hLB using hL
  have hLinj : Function.Injective L := by
    intro x y hxy
    apply Subtype.ext
    ext w
    apply hinj
    rw [← hLf x w, ← hLf y w, hxy]
  have hfixL : ∀ x : ↥E, ∀ d ∈ f '' (U : Set W), L x d = d := by
    rintro x _ ⟨u, hu, rfl⟩
    rw [hLf x u, hEU x x.2 u hu]
  have hD₀ : Nat.card F ^ 3 ≤ Nat.card (f '' (U : Set W)) := by
    rw [Nat.card_image_of_injective hinj]
    exact hU3
  rw [← hF]
  exact card_le_of_isometry_fix L hLinj hLB hfixL hD₀

end CFSG.Quasithin.Vol2.KGNat
