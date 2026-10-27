module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddChainA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseF2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem exists_chiefChain (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) :
    ∃ (r : ℕ) (W : ℕ → Subgroup G), W 0 = Zv α ∧ W r = Wn α ∧
      (∀ i, i ≤ r → stab α ≤ Subgroup.normalizer (W i : Set G)) ∧
      (∀ i, i ≤ r → W i ≤ pCoreOf 2 (stab α)) ∧
      (∀ i j, i ≤ j → j ≤ r → W i ≤ W j) ∧
      ∀ i, i < r → IsChiefStep (stab α) (pCoreOf 2 (stab α)) (W i) (W (i + 1)) := by
  have hZ : IsNormalIn (stab α) (pCoreOf 2 (stab α)) (Zv α) :=
    ⟨Zv_le_Qv hA α, fun g hg z hz =>
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α hg) z).mp hz⟩
  have hWn : IsNormalIn (stab α) (pCoreOf 2 (stab α)) (Wn α) :=
    ⟨hs.Wn_le_Qv hA hb, fun g hg w hw =>
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Wn α hg) w).mp hw⟩
  obtain ⟨r, W, h0, hr, hstep⟩ := Chain.exists_chain hZ hWn (hs.Zv_le_Wn hA h26)
  have hnorm : ∀ i, i ≤ r → IsNormalIn (stab α) (pCoreOf 2 (stab α)) (W i) := by
    intro i hi
    rcases Nat.lt_or_ge i r with h | h
    · exact (hstep i h).2.1
    · rw [show i = r by omega, hr]
      exact hWn
  exact ⟨r, W, h0, hr, fun i hi => Sit43.le_normalizer_of_conj_mem (hnorm i hi).2,
    fun i hi => (hnorm i hi).1, F.chain_mono hstep, hstep⟩

theorem atMostOne_of_transvec (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {x : G} (hx : x ∈ stab α) (hxQ : x ∉ Qv α)
    (h2 : secIdx (Subgroup.zpowers x) (Zv α) (Wn α) ≤ 2) : AtMostOneNoncentral α := by
  obtain ⟨r, W, h0, hr, hXW, hWQ, -, hstep⟩ := exists_chiefChain hA h26 hs hb
  exact ⟨r, W, h0, hr, hstep, (chief_chain_of_le_two (quot_stab_five hA hs.vα) hx hxQ hWQ hXW
    hstep (by rw [h0, hr]; exact h2)).2⟩

theorem atMostOne_of_le_four_of_mem (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {x : G} (hx : x ∈ stab α) (hxQ : x ∉ Qv α)
    (hxL : x ∈ Lres α ⊔ Qv α) (h4 : secIdx (Subgroup.zpowers x) (Zv α) (Wn α) ≤ 4) :
    AtMostOneNoncentral α := by
  obtain ⟨r, W, h0, hr, hXW, hWQ, -, hstep⟩ := exists_chiefChain hA h26 hs hb
  exact ⟨r, W, h0, hr, hstep, Chain.central_or_central_of_le_four (quot_stab_five hA hs.vα) hXW
    hWQ hstep hx hxQ hxL (by rw [h0, hr]; exact h4)⟩

theorem mem_Lres_sup_of_central (hA : F53Amalgam H M S) (hs : Sit43 α) {β : Geo H M}
    (hβ : β ∈ nbrs α) {x : G} (hx : x ∈ stab α) (hxβ : x ∈ stab β)
    (hcen : ∀ g ∈ stab α ⊓ stab β, ⁅x, g⁆ ∈ Qv α) : x ∈ Lres α ⊔ Qv α := by
  obtain ⟨D⟩ := hs.exists_dict hA hβ
  have hψx : D.ψ ⟨x, hx⟩ ∈ S5SylF :=
    (mem_S5Syl_iff _).mp (D.ψ_mem_S5Syl (S := stab α ⊓ stab β) ⟨hx, hxβ⟩)
  have hcomm : ∀ τ ∈ S5SylF, D.ψ ⟨x, hx⟩ * τ = τ * D.ψ ⟨x, hx⟩ := by
    intro τ hτ
    rw [← mem_S5Syl_iff, ← D.bar_S] at hτ
    obtain ⟨g, hg, rfl⟩ := hτ
    have h1 : D.ψ ⁅(⟨x, hx⟩ : ↥(stab α)), g⁆ = 1 := (D.ker_iff _).mpr (hcen g hg)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have heven : D.ψ ⟨x, hx⟩ ∈ alternatingGroup (Fin 5) :=
    Perm.mem_alternatingGroup.mpr (Chain.sign_eq_one_of_central _ hψx hcomm)
  rw [← map_oTwoRes_eq_alt D.surj] at heven
  obtain ⟨l, hl, hlx⟩ := heven
  have hq : ((l⁻¹ * ⟨x, hx⟩ : ↥(stab α)) : G) ∈ Qv α :=
    (D.ker_iff _).mp (by rw [map_mul, map_inv, hlx, inv_mul_cancel])
  have e : x = (l : G) * ((l⁻¹ * ⟨x, hx⟩ : ↥(stab α)) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem_sup hl hq

theorem atMostOne_of_le_four (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {x : G} (hx : x ∈ stab α) (hxQ : x ∉ Qv α)
    (h4 : secIdx (Subgroup.zpowers x) (Zv α) (Wn α) ≤ 4) {β : Geo H M} (hβ : β ∈ nbrs α)
    (hxβ : x ∈ stab β) (hcen : ∀ g ∈ stab α ⊓ stab β, ⁅x, g⁆ ∈ Qv α) :
    AtMostOneNoncentral α :=
  atMostOne_of_le_four_of_mem hA h26 hs hb hx hxQ (mem_Lres_sup_of_central hA hs hβ hx hxβ hcen)
    h4

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
