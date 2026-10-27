module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpElt
public import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative


@[expose] noncomputable def ggSpSigned_permAutHom (p k : ℕ) : Equiv.Perm (Fin k) →*
    MulAut (Fin k → Multiplicative (ZMod p)) where
  toFun := SpCoord.permAut
  map_one' := by
    apply MulEquiv.ext; intro f; funext t; rfl
  map_mul' := by
    intro σ τ
    apply MulEquiv.ext; intro f; funext t; rfl

theorem ggSpSigned_mul_of_mem_spSignedGroup {p k : ℕ}
    (u : Equiv.Perm (Fin k → Multiplicative (ZMod p)))
    (hu : u ∈ SpJoin.spSignedGroup k p) :
    ∀ f g : Fin k → Multiplicative (ZMod p), u (f * g) = u f * u g := by
  refine Subgroup.closure_induction
    (p := fun u _ => ∀ f g : Fin k → Multiplicative (ZMod p), u (f * g) = u f * u g)
    ?_ ?_ ?_ ?_ hu
  · rintro u ⟨i, rfl⟩
    by_cases h : i.val + 1 < k
    · rw [SpJoin.spReflPerm_of_lt k p i h]
      intro f g
      exact (SpCoord.permAut (Equiv.swap i ⟨i.val + 1, h⟩)).map_mul f g
    · rw [SpJoin.spReflPerm_of_not_lt k p i h]
      have hc : ⇑(SpJoin.coordInv k p i) = ⇑(SpCoord.sgnAut i) := rfl
      rw [hc]
      intro f g
      exact (SpCoord.sgnAut i).map_mul f g
  · intro f g
    rfl
  · intro x y hx hy ihx ihy f g
    calc (x * y) (f * g) = x (y (f * g)) := rfl
      _ = x (y f * y g) := by rw [ihy f g]
      _ = x (y f) * x (y g) := ihx (y f) (y g)
      _ = (x * y) f * (x * y) g := rfl
  · intro x hx ih f g
    have h1 : x (x⁻¹ (f * g)) = x (x⁻¹ f * x⁻¹ g) := by
      rw [ih (x⁻¹ f) (x⁻¹ g)]
      simp
    exact Equiv.injective x h1

@[expose] noncomputable def ggSpSigned_rho (p k : ℕ) : ↥(SpJoin.spSignedGroup k p) →*
    MulAut (Fin k → Multiplicative (ZMod p)) where
  toFun u :=
    { toFun := ⇑(u : Equiv.Perm (Fin k → Multiplicative (ZMod p)))
      invFun := ⇑(u : Equiv.Perm (Fin k → Multiplicative (ZMod p))).symm
      left_inv := fun f => (u : Equiv.Perm _).left_inv f
      right_inv := fun f => (u : Equiv.Perm _).right_inv f
      map_mul' := ggSpSigned_mul_of_mem_spSignedGroup (p := p) (k := k)
        (u : Equiv.Perm (Fin k → Multiplicative (ZMod p))) u.2 }
  map_one' := by apply MulEquiv.ext; intro f; rfl
  map_mul' := by intro u v; apply MulEquiv.ext; intro f; rfl

@[simp] theorem ggSpSigned_rho_apply {p k : ℕ} (u : ↥(SpJoin.spSignedGroup k p))
    (f : Fin k → Multiplicative (ZMod p)) :
    ggSpSigned_rho p k u f = (u : Equiv.Perm (Fin k → Multiplicative (ZMod p))) f :=
  rfl

theorem ggSpSigned_rho_injective (p k : ℕ) : Function.Injective (ggSpSigned_rho p k) := by
  intro u v h
  apply Subtype.ext
  apply Equiv.ext
  intro f
  simpa using congrArg (fun w : MulAut (Fin k → Multiplicative (ZMod p)) => w f) h

@[expose] noncomputable def ggSpSigned_spReflAut (p k : ℕ) (i : Fin k) :
    MulAut (Fin k → Multiplicative (ZMod p)) :=
  if h : i.val + 1 < k then SpCoord.permAut (Equiv.swap i ⟨i.val + 1, h⟩)
  else SpCoord.sgnAut i

theorem ggSpSigned_rho_spReflPerm (p k : ℕ) (i : Fin k) :
    ggSpSigned_rho p k ⟨SpJoin.spReflPerm k p i,
        SpJoin.spReflPerm_mem_spSignedGroup k p i⟩ = ggSpSigned_spReflAut p k i := by
  apply MulEquiv.ext; intro f
  rw [ggSpSigned_rho_apply]
  simp only [Subtype.coe_mk]
  by_cases h : i.val + 1 < k
  · rw [SpJoin.spReflPerm_of_lt k p i h]
    simp only [ggSpSigned_spReflAut, dif_pos h]
    rfl
  · rw [SpJoin.spReflPerm_of_not_lt k p i h]
    simp only [ggSpSigned_spReflAut, dif_neg h]
    rfl

theorem ggSpSigned_conj_permAut_sgnAut (p k : ℕ) (τ : Equiv.Perm (Fin k)) (j : Fin k) :
    SpCoord.permAut (p := p) τ * SpCoord.sgnAut (p := p) j *
        (SpCoord.permAut (p := p) τ)⁻¹ = SpCoord.sgnAut (p := p) (τ j) := by
  have hu : ∀ f i, toAdd (SpCoord.permAut (p := p) τ f (τ i)) =
      (1 : ZMod p) * toAdd (f i) := by
    intro f i
    rw [SpCoord.permAut_apply]
    simp
  have h := SpCoord.IsSignedPerm.mul_sgnAut (p := p) (k := k)
    (u := SpCoord.permAut (p := p) τ) (π := τ) (ε := fun _ => 1) hu j
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem ggSpSigned_closure_range_subtype {G : Type*} [Group G] {H : Subgroup G} {ι : Type}
    (s : ι → G) (hs : ∀ i, s i ∈ H) (hH : Subgroup.closure (Set.range s) = H) :
    Subgroup.closure (Set.range fun i => (⟨s i, hs i⟩ : H)) = ⊤ := by
  have hmap : Subgroup.map (Subgroup.subtype H)
      (Subgroup.closure (Set.range fun i => (⟨s i, hs i⟩ : H))) = H := by
    rw [MonoidHom.map_closure]
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨y, ⟨i, rfl⟩, rfl⟩
      exact hs i
    · calc H = Subgroup.closure (Set.range s) := hH.symm
        _ ≤ Subgroup.closure
              (Subgroup.subtype H '' Set.range (fun i => (⟨s i, hs i⟩ : H))) :=
            Subgroup.closure_mono (by
              rintro _ ⟨i, rfl⟩
              exact ⟨⟨s i, hs i⟩, ⟨i, rfl⟩, rfl⟩)
  apply le_antisymm le_top
  intro x _
  have hx : (x : G) ∈ Subgroup.map (Subgroup.subtype H)
      (Subgroup.closure (Set.range fun i => (⟨s i, hs i⟩ : H))) := by
    rw [hmap]; exact x.2
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hyx' : y = x := Subgroup.subtype_injective H hyx
  rwa [← hyx']

theorem ggSpSigned_ggIsReflection_congr {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] {A : Subgroup G} {V : Type} [Group V] (Θ : V ≃* ↥A)
    {s : MulAut V} (hs2 : s ^ 2 = 1)
    (hfix : Nat.card {f : V // s f = f} * p = Nat.card V) :
    GGIsReflection p (MulAut.congr Θ s) :=
  ⟨by rw [← map_pow, hs2, map_one],
    (ggIsPseudoReflection_congr Θ (pow_sub_one_eq_one_of_sq hp hp2 hs2) hfix).2⟩

theorem ggSpSigned_isSignedPerm_mem_range {p k : ℕ} (hk : 1 ≤ k)
    {u : MulAut (Fin k → Multiplicative (ZMod p))} (hu : IsSignedPerm ⇑u) :
    u ∈ (ggSpSigned_rho p k).range := by
  classical
  have hlast : ¬ (⟨k - 1, by omega⟩ : Fin k).val + 1 < k := by
    simp only [Fin.val_mk]; omega
  have hlast_dif : ggSpSigned_spReflAut p k ⟨k - 1, by omega⟩ =
      SpCoord.sgnAut ⟨k - 1, by omega⟩ := by
    simp only [ggSpSigned_spReflAut, dif_neg hlast]
  let gen : Fin k → ↥(SpJoin.spSignedGroup k p) := fun i =>
    ⟨SpJoin.spReflPerm k p i, SpJoin.spReflPerm_mem_spSignedGroup k p i⟩
  let K : Subgroup (Equiv.Perm (Fin k)) :=
    (ggSpSigned_rho p k).range.comap (ggSpSigned_permAutHom p k)
  have hadj : ∀ (i : Fin k) (h : i.val + 1 < k),
      Equiv.swap i ⟨i.val + 1, h⟩ ∈ K := by
    intro i h
    rw [Subgroup.mem_comap]
    have hρ := ggSpSigned_rho_spReflPerm (p := p) (k := k) i
    have hr : ggSpSigned_spReflAut p k i =
        SpCoord.permAut (Equiv.swap i ⟨i.val + 1, h⟩) := by
      simp only [ggSpSigned_spReflAut, dif_pos h]
    have hgg : (ggSpSigned_permAutHom p k) (Equiv.swap i ⟨i.val + 1, h⟩) =
        ggSpSigned_rho p k (gen i) := by
      rw [hρ, hr]
      rfl
    rw [hgg]
    exact ⟨gen i, rfl⟩
  have hswapK : ∀ a b : Fin k, Equiv.swap a b ∈ K := by
    suffices hall : ∀ a b : Fin k, a.val ≤ b.val → Equiv.swap a b ∈ K by
      intro a b
      rcases le_total a.val b.val with h | h
      · exact hall a b h
      · rw [Equiv.swap_comm]
        exact hall b a h
    intro a b hab
    have key : ∀ d, ∀ a b : Fin k, a.val ≤ b.val → b.val - a.val = d →
        Equiv.swap a b ∈ K := by
      intro d
      induction d using Nat.strongRecOn with
      | ind d ih =>
        intro a b hab hd
        by_cases h0 : d = 0
        · have hab' : a = b := Fin.ext (by omega)
          subst hab'
          rw [Equiv.swap_self a]
          exact K.one_mem
        · have hlt : a.val < b.val := by omega
          have ha' : a.val + 1 < k := by omega
          have hdiff : b.val - (⟨a.val + 1, ha'⟩ : Fin k).val = d - 1 := by
            simp only [Fin.val_mk]; omega
          have hdlt : d - 1 < d := Nat.sub_lt (Nat.pos_of_ne_zero h0) (by omega)
          have hle' : (⟨a.val + 1, ha'⟩ : Fin k).val ≤ b.val := by
            simp only [Fin.val_mk]; omega
          have h1 : Equiv.swap a ⟨a.val + 1, ha'⟩ ∈ K := hadj a ha'
          have h2 : Equiv.swap ⟨a.val + 1, ha'⟩ b ∈ K :=
            ih (d - 1) hdlt ⟨a.val + 1, ha'⟩ b hle' hdiff
          exact SubmonoidClass.swap_mem_trans K.toSubmonoid h1 h2
    exact key (b.val - a.val) a b hab rfl
  have hpermMem : ∀ a b : Fin k, SpCoord.permAut (Equiv.swap a b) ∈ (ggSpSigned_rho p k).range :=
    fun a b => hswapK a b
  have hsgnLast : SpCoord.sgnAut (⟨k - 1, by omega⟩ : Fin k) ∈ (ggSpSigned_rho p k).range := by
    have hρ := ggSpSigned_rho_spReflPerm (p := p) (k := k) ⟨k - 1, by omega⟩
    have : ggSpSigned_rho p k (gen ⟨k - 1, by omega⟩) =
        SpCoord.sgnAut ⟨k - 1, by omega⟩ := by rw [hρ, hlast_dif]
    rw [← this]
    exact ⟨gen _, rfl⟩
  have hsgn : ∀ i : Fin k, SpCoord.sgnAut i ∈ (ggSpSigned_rho p k).range := by
    intro i
    have hconj := ggSpSigned_conj_permAut_sgnAut (p := p) (k := k)
      (Equiv.swap i ⟨k - 1, by omega⟩) (⟨k - 1, by omega⟩ : Fin k)
    rw [Equiv.swap_apply_right] at hconj
    rw [← hconj]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (hpermMem i ⟨k - 1, by omega⟩) hsgnLast)
      (Subgroup.inv_mem _ (hpermMem i ⟨k - 1, by omega⟩))
  exact SpCoord.mem_of_isSignedPerm hsgn (fun a b _ => hpermMem a b) hu

end CFSG.StandardType

end
