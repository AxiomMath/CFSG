module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModel
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGWPlusPositionRk
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

private theorem ggS8a_eq_of_forall_inv_mul_mem_of_perfect {L' : Type} [Group L'] {Z : Subgroup L'}
    (hZ : Z ≤ Subgroup.center L') (hperf : commutator L' = ⊤) {φ₁ φ₂ : MulAut L'}
    (h : ∀ l, (φ₁ l)⁻¹ * φ₂ l ∈ Z) : φ₁ = φ₂ := by
  have hcen : ∀ y ∈ Z, ∀ g : L', g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hZ hy) g
  letI : CommGroup Z :=
    { (inferInstance : Group Z) with mul_comm := fun x y => Subtype.ext (hcen y y.2 x) }
  let f : L' →* Z :=
    { toFun := fun l => ⟨(φ₁ l)⁻¹ * φ₂ l, h l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun l m => Subtype.ext (by
        show (φ₁ (l * m))⁻¹ * φ₂ (l * m) = (φ₁ l)⁻¹ * φ₂ l * ((φ₁ m)⁻¹ * φ₂ m)
        have hc := hcen _ (h l) (φ₁ m)⁻¹
        calc (φ₁ (l * m))⁻¹ * φ₂ (l * m) = (φ₁ m)⁻¹ * ((φ₁ l)⁻¹ * φ₂ l) * φ₂ m := by
              rw [map_mul, map_mul]; group
          _ = (φ₁ l)⁻¹ * φ₂ l * (φ₁ m)⁻¹ * φ₂ m := by rw [hc]
          _ = (φ₁ l)⁻¹ * φ₂ l * ((φ₁ m)⁻¹ * φ₂ m) := by group) }
  have hf : ∀ l, f l = 1 := fun l =>
    Abelianization.commutator_subset_ker f (by rw [hperf]; exact Subgroup.mem_top l)
  ext l
  exact inv_mul_eq_one.mp (congrArg Subtype.val (hf l))

private theorem ggS8a_mem_Z_iff {L' : Type} [Group L'] (Z : Subgroup L')
    (hZ : ∀ z : L', z ∈ Z ↔ z ∈ Subgroup.center L' ∧ ∃ k : ℕ, z ^ 2 ^ k = 1)
    (a : MulAut L') (z : L') : z ∈ Z ↔ a z ∈ Z := by
  rw [hZ z, hZ (a z)]
  constructor
  · rintro ⟨hzcen, k, hk⟩
    refine ⟨?_, k, ?_⟩
    · rw [Subgroup.mem_center_iff] at hzcen ⊢
      intro g
      obtain ⟨g', rfl⟩ := a.surjective g
      rw [← map_mul, ← map_mul, hzcen g']
    · rw [← map_pow, hk, map_one]
  · rintro ⟨hacen, k, hk⟩
    refine ⟨?_, k, ?_⟩
    · rw [Subgroup.mem_center_iff] at hacen ⊢
      intro g
      apply a.injective
      rw [map_mul, map_mul]
      exact hacen (a g)
    · have h1 : a (z ^ 2 ^ k) = 1 := by rw [map_pow]; exact hk
      exact a.injective (by simpa using h1)

private theorem ggS8a_map_Z_eq {L' : Type} [Group L'] (Z : Subgroup L')
    (hZ : ∀ z : L', z ∈ Z ↔ z ∈ Subgroup.center L' ∧ ∃ k : ℕ, z ^ 2 ^ k = 1)
    (a : MulAut L') : Z.map a.toMonoidHom = Z := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (ggS8a_mem_Z_iff Z hZ a z).mp hz
  · intro hy
    refine ⟨a⁻¹ y, ?_, ?_⟩
    · exact (ggS8a_mem_Z_iff Z hZ a (a⁻¹ y)).mpr (by simpa using hy)
    · simp

theorem exists_model_quotient_six_one
    {p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ 1 + 1) (hpd : p ∣ 6)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1))) θ hE)
    (hr : p ^ (6 - 1) ≤ Nat.card E)
    (Z : Subgroup L') [Z.Normal]
    (hZ : ∀ z : L', z ∈ Z ↔ z ∈ Subgroup.center L' ∧ ∃ k : ℕ, z ^ 2 ^ k = 1) :
    ∃ φ : ↥(unitarySU 2 1 K 6) →* L' ⧸ Z, UnitTB.Model φ ∧
      ∀ e : E, ∃ (t : Fin 6 → K) (D : GL (Fin 6) K)
        (hD : D ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K))),
        (D : Matrix (Fin 6) (Fin 6) K) = diagonal t ∧
        ∀ (s : ↥(unitarySU 2 1 K 6)) (l : L'), (QuotientGroup.mk l : L' ⧸ Z) = φ s →
          (QuotientGroup.mk (L'.normalizerMonoidHom ⟨e, hE e.2⟩ l) : L' ⧸ Z) =
            φ (conjN D hD s) := by
  classical
  have hp3 : p = 3 := by
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) (by simpa using hpq)
    have hge : 2 ≤ p := hp.two_le
    have hpne2 : p ≠ 2 := by
      intro h2
      rw [h2] at hpq
      norm_num at hpq
    omega
  have hperf : commutator L' = ⊤ := hpos.1
  have hEA : IsElemAbelian p E := hpos.2.1
  have hZc : Z ≤ Subgroup.center L' := fun z hz => ((hZ z).mp hz).1
  have hZker : Z ≤ (ggQuotHom θ).ker := fun z hz => by
    rw [ker_ggQuotHom]; exact hZc hz
  let ψstar : L' ⧸ Z →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    QuotientGroup.lift Z (ggQuotHom θ) hZker
  have hψmk : ∀ l : L', ψstar (l : L' ⧸ Z) = ggQuotHom θ l :=
    fun l => QuotientGroup.lift_mk' Z hZker l
  have hψs : Function.Surjective ψstar := by
    intro r
    obtain ⟨l, hl⟩ := ggQuotHom_surjective θ r
    exact ⟨(l : L' ⧸ Z), by rw [hψmk]; exact hl⟩
  have hkerlift : ψstar.ker = (Subgroup.center L').map (QuotientGroup.mk' Z) := by
    have h := QuotientGroup.ker_lift (N := Z) (ggQuotHom θ) hZker
    rwa [ker_ggQuotHom] at h
  have hker : ψstar.ker ≤ Subgroup.center (L' ⧸ Z) := by
    rw [hkerlift]
    rintro _ ⟨z, hz, rfl⟩
    have hzc : ∀ g : L', g * z = z * g := Subgroup.mem_center_iff.mp hz
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    change (l : L' ⧸ Z) * (z : L' ⧸ Z) = (z : L' ⧸ Z) * (l : L' ⧸ Z)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hzc l]
  have hodd : Odd (Nat.card ψstar.ker) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    have h2 : 2 ∣ Nat.card ψstar.ker :=
      Nat.dvd_of_mod_eq_zero (by rwa [Nat.even_iff] at hev)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hg2 : (g : L' ⧸ Z) ^ 2 = 1 := by
      have h := (orderOf_eq_prime_iff.mp hg).1
      simpa using congrArg Subtype.val h
    have hgne : g ≠ 1 := (orderOf_eq_prime_iff.mp hg).2
    have hgmap : (g : L' ⧸ Z) ∈ (Subgroup.center L').map (QuotientGroup.mk' Z) := by
      rw [← hkerlift]
      exact g.2
    obtain ⟨w, hwcen, hw⟩ := Subgroup.mem_map.mp hgmap
    have hw2 : w ^ 2 ∈ Z := by
      rw [← QuotientGroup.eq_one_iff (w ^ 2)]
      change (QuotientGroup.mk' Z (w ^ 2) : L' ⧸ Z) = 1
      rw [map_pow, hw]
      exact hg2
    obtain ⟨-, k, hk⟩ := (hZ (w ^ 2)).mp hw2
    have hwZ : w ∈ Z := by
      refine (hZ w).mpr ⟨hwcen, ⟨k + 1, ?_⟩⟩
      have h1 : w ^ (2 * 2 ^ k) = 1 := by
        rw [pow_mul]; exact hk
      simpa [pow_succ, Nat.mul_comm] using h1
    have : (g : L' ⧸ Z) = 1 := by
      rw [← hw]
      exact (QuotientGroup.eq_one_iff w).mpr hwZ
    exact hgne (Subtype.ext this)
  have hperf' : commutator (L' ⧸ Z) = ⊤ := by
    have hrange : (QuotientGroup.mk' Z).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Z)
    have hmap := Subgroup.map_commutator (QuotientGroup.mk' Z)
      (H₁ := (⊤ : Subgroup L')) (H₂ := (⊤ : Subgroup L'))
    simp only [Subgroup.map_top, hrange] at hmap
    rw [commutator_def, ← hmap, ← commutator_def, hperf, Subgroup.map_top]
    exact hrange
  let Γf : E → MulAut (L' ⧸ Z) := fun e =>
    QuotientGroup.congr Z Z ((ggGamma L' hE) e) (ggS8a_map_Z_eq Z hZ ((ggGamma L' hE) e))
  have hΓf : ∀ (e : E) (l : L'), Γf e (l : L' ⧸ Z) =
      (((ggGamma L' hE) e l : L') : L' ⧸ Z) :=
    fun e l => QuotientGroup.congr_mk _ _ _ _ l
  let Γ : E →* MulAut (L' ⧸ Z) :=
    { toFun := Γf
      map_one' := by
        ext x
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
        rw [hΓf, map_one, MulAut.one_apply, MulAut.one_apply]
      map_mul' := fun e f => by
        ext x
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
        simp only [MulAut.mul_apply, hΓf, map_mul] }
  set Astar : Subgroup (MulAut (L' ⧸ Z)) := Γ.range with hAdef
  have hA : IsElemAbelian 3 Astar := by
    rw [hAdef]
    exact isElemAbelian_range
      (fun a b : E => Subtype.ext (IsElemAbelian.comm hEA a.2 b.2))
      (fun a : E => Subtype.ext (by
        have h := hEA.2 a.1 a.2
        rwa [hp3] at h)) Γ
  have hkerΓ : Γ.ker ≤ (E ⊓ Subgroup.centralizer (L' : Set M)).subgroupOf E := by
    intro e he
    rw [MonoidHom.mem_ker] at he
    have hgg : (ggGamma L' hE) e = 1 :=
      ggS8a_eq_of_forall_inv_mul_mem_of_perfect hZc hperf (fun l => by
        have hc := congrArg (fun f : MulAut (L' ⧸ Z) => f (l : L' ⧸ Z)) he
        have hc' : Γf e (l : L' ⧸ Z) = (l : L' ⧸ Z) := hc
        rw [hΓf e l] at hc'
        exact QuotientGroup.eq.mp hc')
    rw [Subgroup.mem_subgroupOf]
    exact ⟨e.2, (ggGamma_eq_one_iff L' hE e).mp hgg⟩
  have hkerΓcard : Nat.card Γ.ker ≤ p := by
    have hle : Γ.ker ≤ (E ⊓ Subgroup.centralizer (L' : Set M)).subgroupOf E := hkerΓ
    have h1 : Nat.card Γ.ker ≤
        Nat.card ↥((E ⊓ Subgroup.centralizer (L' : Set M)).subgroupOf E) :=
      Nat.card_le_card_of_injective
        (fun x : Γ.ker =>
          (⟨x.1, hle x.2⟩ : (E ⊓ Subgroup.centralizer (L' : Set M)).subgroupOf E))
        (fun a b h => Subtype.ext (congrArg
          (fun x : (E ⊓ Subgroup.centralizer (L' : Set M)).subgroupOf E => (x : ↥E)) h))
    have h2 : Nat.card ↥((E ⊓ Subgroup.centralizer (L' : Set M)).subgroupOf E) =
        Nat.card ↥(E ⊓ Subgroup.centralizer (L' : Set M)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h2] at h1
    exact le_trans h1 (TableBBridge.card_inf_centralizer_le hpos hp)
  have hcard : 3 ^ 4 ≤ Nat.card Astar := by
    have h5 : p ^ 5 ≤ Nat.card E := by simpa using hr
    have hcardE : Nat.card E = Nat.card Γ.range * Nat.card Γ.ker :=
      (TableB.card_range_mul_card_ker Γ).symm
    rw [hcardE] at h5
    have hmul : p ^ 4 * p ≤ Nat.card Γ.range * p :=
      calc p ^ 4 * p = p ^ 5 := by ring
        _ ≤ Nat.card Γ.range * Nat.card Γ.ker := h5
        _ ≤ Nat.card Γ.range * p := Nat.mul_le_mul_left _ hkerΓcard
    have hpow : p ^ 4 ≤ Nat.card Γ.range := Nat.le_of_mul_le_mul_right hmul hp.pos
    rw [← hp3]
    simpa [hAdef] using hpow
  have hAI : ∀ a ∈ Astar, ∃ x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      ∀ l : L' ⧸ Z, x (ψstar l) = ψstar (a l) := by
    rintro a ⟨e, rfl⟩
    refine ⟨ggLAut L' θ ⟨e, hE e.2⟩, hpos.2.2.2.1 e, ?_⟩
    intro l
    obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective l
    show ggLAut L' θ ⟨e, hE e.2⟩ (ψstar (l' : L' ⧸ Z)) =
      ψstar (Γf e (l' : L' ⧸ Z))
    rw [hΓf]
    rw [hψmk, hψmk]
    rw [ggQuotHom_apply, ggLAut_apply, ggQuotHom_apply]
    rfl
  obtain ⟨φ, hmodel, hdiag⟩ :=
    USixTwo.exists_diagModel_odd hK hψs hker hperf' hodd hA hAI hcard
  refine ⟨φ, hmodel, ?_⟩
  intro e
  obtain ⟨t, D, hD, hDt, hact⟩ := hdiag (Γ e) ⟨e, rfl⟩
  refine ⟨t, D, hD, hDt, ?_⟩
  intro s l hsl
  calc (QuotientGroup.mk (L'.normalizerMonoidHom ⟨e, hE e.2⟩ l) : L' ⧸ Z)
      = Γf e (l : L' ⧸ Z) := (hΓf e l).symm
    _ = Γ e (l : L' ⧸ Z) := rfl
    _ = Γ e (φ s) := by rw [hsl]
    _ = φ (conjN D hD s) := hact s

end CFSG.StandardType
