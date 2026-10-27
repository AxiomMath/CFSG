module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413SpFix
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413Emb
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413AutX
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413StrAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.Open CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag Subgroup

private theorem a1413SpData_spIota_injective {Q : Type} [Group Q] {L : Subgroup Q}
    {K : Type} [Field K] (e : ↥L ≃* StatedProj (StatedSp 2 K)) :
    Function.Injective (spIota e) := by
  intro x y h
  exact e.symm.injective (Subtype.ext h)

private theorem a1413SpData_spIota_apply_e {Q : Type} [Group Q] {L : Subgroup Q}
    {K : Type} [Field K] (e : ↥L ≃* StatedProj (StatedSp 2 K)) (l : ↥L) :
    spIota e (e l) = (l : Q) := by
  simp [spIota]

private theorem a1413SpData_theta_iota {Q : Type} [Group Q] {L : Subgroup Q} (hLn : L.Normal)
    {K : Type} [Field K] (e : ↥L ≃* StatedProj (StatedSp 2 K))
    (θ : Q →* MulAut (StatedProj (StatedSp 2 K)))
    (hθapp : ∀ (q : Q) (l : ↥L), θ q (e l) = e ⟨q * l * q⁻¹, hLn.conj_mem _ l.2 q⟩)
    (q : Q) (x : StatedProj (StatedSp 2 K)) :
    spIota e (θ q x) = q * spIota e x * q⁻¹ := by
  have h : θ q x = e ⟨q * (e.symm x) * q⁻¹, hLn.conj_mem _ (e.symm x).2 q⟩ := by
    rw [← hθapp q (e.symm x), e.apply_symm_apply]
  rw [h, a1413SpData_spIota_apply_e]
  rfl

private theorem a1413SpData_theta_u1 {Q : Type} [Group Q] {L : Subgroup Q} (hLn : L.Normal)
    {K : Type} [Field K] (e : ↥L ≃* StatedProj (StatedSp 2 K))
    (θ : Q →* MulAut (StatedProj (StatedSp 2 K)))
    (hθapp : ∀ (q : Q) (l : ↥L), θ q (e l) = e ⟨q * l * q⁻¹, hLn.conj_mem _ l.2 q⟩)
    {a : Q} (haz : a * spIota e (u1 K) = spIota e (u1 K) * a) :
    θ a (u1 K) = u1 K := by
  have hz : a * (e.symm (u1 K) : Q) * a⁻¹ = (e.symm (u1 K) : Q) := by
    change a * spIota e (u1 K) * a⁻¹ = spIota e (u1 K)
    rw [haz]
    group
  have hz' : (⟨a * (e.symm (u1 K)) * a⁻¹, hLn.conj_mem _ (e.symm (u1 K)).2 a⟩ : ↥L) =
      e.symm (u1 K) := Subtype.ext hz
  have h := hθapp a (e.symm (u1 K))
  rw [e.apply_symm_apply, hz', e.apply_symm_apply] at h
  exact h

private theorem a1413SpData_theta_mem_X0 {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (h4 : 4 ≤ Nat.card K) (θ : MulAut (StatedProj (StatedSp 2 K))) (hθu1 : θ (u1 K) = u1 K)
    {x : StatedProj (StatedSp 2 K)} (hx : x ∈ X0 K) : θ x ∈ X0 K := by
  have hCmap : (centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))).map θ.toMonoidHom =
      centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))) := by
    rw [a1413StrMapCentralizerSingleton, hθu1]
  have hx' : x ∈ ⁅centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))),
      centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))⁆ := by
    rwa [a1413StrCommutator_C_eq_X0 h2 h4]
  have hmem : θ x ∈ (⁅centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))),
      centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))⁆).map θ.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨x, hx', rfl⟩
  rw [Subgroup.map_commutator, hCmap, a1413StrCommutator_C_eq_X0 h2 h4] at hmem
  exact hmem

private theorem a1413SpData_theta_fixes_E1 {Q : Type} [Group Q] {L : Subgroup Q}
    (hLn : L.Normal) {K : Type} [Field K] (e : ↥L ≃* StatedProj (StatedSp 2 K))
    (θ : Q →* MulAut (StatedProj (StatedSp 2 K)))
    (hθapp : ∀ (q : Q) (l : ↥L), θ q (e l) = e ⟨q * l * q⁻¹, hLn.conj_mem _ l.2 q⟩)
    {c : Q} (hc : c ∈ centralizer (((E1 K).map (spIota e) : Subgroup Q) : Set Q))
    {x : StatedProj (StatedSp 2 K)} (hx : x ∈ E1 K) : θ c x = x := by
  have hιx : spIota e x ∈ (E1 K).map (spIota e) := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hfix : c * spIota e x * c⁻¹ = spIota e x := by
    have h := (Subgroup.mem_centralizer_iff.mp hc) (spIota e x) hιx
    rw [← h]
    group
  have h := a1413SpData_theta_iota hLn e θ hθapp c x
  rw [hfix] at h
  exact a1413SpData_spIota_injective e h

private theorem a1413SpData_mem_E2_sq_eq_one {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {y : StatedProj (StatedSp 2 K)} (hy : y ∈ E2 K) (hyy : y * y = 1) :
    y = 1 ∨ y = u1 K := by
  by_cases h1 : y = 1
  · exact Or.inl h1
  · right
    have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hyy) h1
    exact eq_u1_of_mem_E2 h2 hy hord

theorem asch1413_sp4_data {Q : Type} [Group Q] [Finite Q] {L A : Subgroup Q} (hLn : L.Normal)
    (hc : centralizer (L : Set Q) ≤ L) {K : Type} [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* StatedProj (StatedSp 2 K)) (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A)
    (hAz : ∀ a ∈ A, a * spIota e (u1 K) = spIota e (u1 K) * a) (hzA : spIota e (u1 K) ∉ A) :
    (∀ a ∈ A, ∀ x ∈ (X0 K).map (spIota e), a * x * a⁻¹ ∈ (X0 K).map (spIota e)) ∧
      A ⊓ centralizer (((E1 K).map (spIota e) : Subgroup Q) : Set Q) = ⊥ ∧
      centralizer (((E1 K).map (spIota e) : Subgroup Q) : Set Q) ≤ (E2 K).map (spIota e) := by
  have h2 : (2 : K) ≠ 0 := CFSG.ComponentClassification.CatFactsSp4.two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have hP : Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e, hZ,
      Subgroup.map_bot]
  obtain ⟨θ, hθinj, hθconj, hθapp, -, -⟩ := a1413_embedding hLn hc e hP
  have hθu1 : ∀ a : Q, a * spIota e (u1 K) = spIota e (u1 K) * a → θ a (u1 K) = u1 K :=
    fun a haz => a1413SpData_theta_u1 hLn e θ hθapp haz
  have hθι : ∀ (q : Q) (x : StatedProj (StatedSp 2 K)),
      spIota e (θ q x) = q * spIota e x * q⁻¹ :=
    fun q x => a1413SpData_theta_iota hLn e θ hθapp q x
  have hθconjy : ∀ y : StatedProj (StatedSp 2 K), θ (spIota e y) = MulAut.conj y := by
    intro y
    have h := hθconj (e.symm y)
    simpa [spIota] using h
  refine ⟨?_, ?_, ?_⟩
  · intro a ha x hx
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    have hX0 : θ a x₀ ∈ X0 K :=
      a1413SpData_theta_mem_X0 h2 h4 (θ a) (hθu1 a (hAz a ha)) hx₀
    rw [← hθι a x₀]
    exact Subgroup.mem_map.mpr ⟨θ a x₀, hX0, rfl⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨haA, hacent⟩ := Subgroup.mem_inf.mp ha
    have hfix : ∀ x ∈ E1 K, θ a x = x := fun x hx =>
      a1413SpData_theta_fixes_E1 hLn e θ hθapp hacent hx
    obtain ⟨y, hy, hαy⟩ := psp4_aut_fix_E1 hodd h5 (θ a) hfix
    have hay : spIota e y = a := by
      apply hθinj
      rw [hθconjy y, hαy]
    have ha2 : a * a = 1 := by
      have h := hAe.2 a haA
      rwa [pow_two] at h
    have hyy : y * y = 1 := by
      apply a1413SpData_spIota_injective e
      rw [map_mul, hay, ha2, map_one]
    rcases a1413SpData_mem_E2_sq_eq_one h2 hy hyy with hy1 | hyu
    · rw [← hay, hy1, map_one]
    · exact absurd (by rw [← hyu, hay]; exact haA) hzA
  · intro c hcent
    have hfix : ∀ x ∈ E1 K, θ c x = x := fun x hx =>
      a1413SpData_theta_fixes_E1 hLn e θ hθapp hcent hx
    obtain ⟨y, hy, hαy⟩ := psp4_aut_fix_E1 hodd h5 (θ c) hfix
    have hcy : c = spIota e y := by
      apply hθinj
      rw [hθconjy y, hαy]
    rw [hcy]
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
