module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltAct
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltRank
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltSix
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Concl
import CFSG.LocalAnalysis.UniquenessCase.UC6K316Frame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup Equiv Equiv.Perm

namespace Alt36

theorem eq_one_or_eq_swap {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b) {g : Perm α}
    (hg : ∀ x, x ≠ a → x ≠ b → g x = x) : g = 1 ∨ g = swap a b := by
  have key : ∀ x, x = a ∨ x = b → g x = a ∨ g x = b := by
    intro x hx
    by_contra hcon
    simp only [not_or] at hcon
    have h2 : g x = x := g.injective (hg (g x) hcon.1 hcon.2)
    rcases hx with rfl | rfl
    · exact hcon.1 h2
    · exact hcon.2 h2
  rcases key a (Or.inl rfl) with ha | ha
  · left
    have hb : g b = b := by
      rcases key b (Or.inr rfl) with hb | hb
      · exact absurd (g.injective (hb.trans ha.symm)) (Ne.symm hab)
      · exact hb
    ext x
    by_cases hxa : x = a
    · rw [hxa, ha]
      rfl
    · by_cases hxb : x = b
      · rw [hxb, hb]
        rfl
      · rw [hg x hxa hxb]
        rfl
  · right
    have hb : g b = a := by
      rcases key b (Or.inr rfl) with hb | hb
      · exact hb
      · exact absurd (g.injective (hb.trans ha.symm)) (Ne.symm hab)
    ext x
    by_cases hxa : x = a
    · rw [hxa, ha, swap_apply_left]
    · by_cases hxb : x = b
      · rw [hxb, hb, swap_apply_right]
      · rw [hg x hxa hxb, swap_apply_of_ne_of_ne hxa hxb]

variable {G : Type} [Group G] [Finite G] (L : Subgroup G) [L.Normal] {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
  (φ : ↥L ⧸ center ↥L ≃* alternatingGroup (Fin n))

theorem coe_phi_mk_conj (g y : G) (hy : y ∈ L) (hy' : g * y * g⁻¹ ∈ L) :
    ((φ (QuotientGroup.mk ⟨g * y * g⁻¹, hy'⟩) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      theta L hn hn6 φ g * (φ (QuotientGroup.mk ⟨y, hy⟩) : Perm (Fin n)) * (theta L hn hn6 φ g)⁻¹ := by
  rw [← psi_apply_coe L hn hn6 φ, Odd.psi_apply_mk, Odd.actHom_apply_mk]
  congr 3

theorem inducesTransposition_of_theta (L : Subgroup G) [L.Normal] (hZ : center ↥L = ⊥) (hn : 5 ≤ 11)
    (hn6 : (11 : ℕ) ≠ 6) (φ : ↥L ⧸ center ↥L ≃* alternatingGroup (Fin 11)) {t : G} {τ : Perm (Fin 11)}
    (hτ : τ.IsSwap) (ht : theta L hn hn6 φ t = τ) : UC6.InducesTransposition t L := by
  have htN : t ∈ normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
    exact Subgroup.mem_top t
  set ψ : ↥L →* alternatingGroup (Fin 11) := φ.toMonoidHom.comp (QuotientGroup.mk' (center ↥L))
  have hker : ψ.ker = center ↥L := by
    ext x
    simp [ψ, MonoidHom.mem_ker]
  have hψ : Function.Bijective ψ :=
    ⟨(MonoidHom.ker_eq_bot_iff ψ).1 (hker.trans hZ), φ.surjective.comp (QuotientGroup.mk'_surjective _)⟩
  refine ⟨htN, MulEquiv.ofBijective ψ hψ, τ, hτ, fun x => ?_⟩
  change ((φ (QuotientGroup.mk (UC6.conjOn L htN x)) : alternatingGroup (Fin 11)) : Perm (Fin 11)) =
    τ * (φ (QuotientGroup.mk x) : Perm (Fin 11)) * τ⁻¹
  rw [← ht]
  exact coe_phi_mk_conj L hn hn6 φ t x.1 x.2 _

end Alt36

namespace Hyp36

open Alt36 Odd

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

theorem alt_conclusion (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) {n : ℕ} (φ : ↥L ⧸ center ↥L ≃* alternatingGroup (Fin n)) (hn : 5 ≤ n)
    (h3 : 13 ≤ n → twoLocalPrimeRank 3 G ≤ 3) :
    p = 3 ∧ n = 11 ∧ center ↥L = ⊥ ∧ ∃ t ∈ pCoreOf 2 M, UC6.InducesTransposition t L ∧
      (∃ y ∈ L, t * y * t⁻¹ ≠ y) ∧
      ∀ q ∈ pCoreOf 2 M, (∀ y ∈ L, q * y * q⁻¹ = y) ∨ (∀ y ∈ L, q * y * q⁻¹ = t * y * t⁻¹) := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLc : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  have hLM : ¬ L ≤ M := fun hLM => h.false_of_component_le hL hne hLM
  have hn6 : n ≠ 6 := by
    rintro rfl
    exact h.false_of_alt_six hL hne φ
  have hn12 : n ≤ 12 := by
    by_contra hcon
    have h13 : 13 ≤ n := by omega
    have h4 := four_le_twoLocalPrimeRank_of_thirteen_le L φ h13
    have h3' := h3 h13
    omega
  set θ : G →* Perm (Fin n) := theta L hn hn6 φ with hθ
  have hfaith : ∀ e ∈ E, θ e = 1 → e = 1 := by
    intro e he hθe
    by_contra he1
    exact hLM (h.le_of_not_faithful L hLc he he1 ((theta_eq_one_iff L hn hn6 φ e).1 hθe))
  have hEtelem : IsElemAbelian p (E.map θ) := CFSG.SectionRank.isElemAbelian_map h.elem θ
  have hEtcard : Nat.card (E.map θ) = p ^ 2 := by
    rw [card_map_of_faithful θ hfaith, h.card]
  obtain ⟨e₀, he₀, he₀1, q₀, hq₀, hq₀e, y₀, hy₀, hy₀'⟩ := h.exists_centralizer_act_nontrivially hLc hne
  have hθq₀ : θ q₀ ≠ 1 := fun h1 => hy₀' ((theta_eq_one_iff L hn hn6 φ q₀).1 h1 y₀ hy₀)
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hRe2 : ∀ e : G, IsPGroup 2 ↥((pCoreOf 2 M).map θ ⊓
      Subgroup.centralizer ({θ e} : Set (Perm (Fin n)))) := fun e => (hQ2.map θ).to_le inf_le_left
  have hReσ : ∀ e : G, ∀ r ∈ (pCoreOf 2 M).map θ ⊓ Subgroup.centralizer ({θ e} : Set (Perm (Fin n))),
      r * θ e = θ e * r := fun e r hr => Subgroup.mem_centralizer_singleton_iff.1 hr.2
  have hpow : ∀ e ∈ E, θ e ^ p = 1 := fun e he => by rw [← map_pow, h.elem.2 e he, map_one]
  have hmemR : ∀ e q : G, q ∈ pCoreOf 2 M → q * e = e * q →
      θ q ∈ (pCoreOf 2 M).map θ ⊓ Subgroup.centralizer ({θ e} : Set (Perm (Fin n))) := by
    intro e q hq hqe
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem θ hq, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, hqe]
  have hR₀1 : (pCoreOf 2 M).map θ ⊓ Subgroup.centralizer ({θ e₀} : Set (Perm (Fin n))) ≠ ⊥ := by
    intro hbot
    have hmem := hmemR e₀ q₀ hq₀ hq₀e
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hθq₀ hmem
  have hfix₀ := card_compl_support_of_normalized h.prime h.odd (hpow e₀ he₀) (hRe2 e₀) (hReσ e₀)
    (h.normalizes_centralizer_qbar L hn hn6 φ he₀ he₀1) hR₀1
  have hσ₀1 : θ e₀ ≠ 1 := fun h1 => he₀1 (hfaith e₀ he₀ h1)
  have hcard12 : Fintype.card (Fin n) ≤ 12 := by
    rw [Fintype.card_fin]
    exact hn12
  rcases plane_dichotomy h.prime h.odd hEtelem hEtcard hcard12 (Subgroup.mem_map_of_mem θ he₀) hσ₀1 hfix₀ with
    hA | ⟨hp3, hn11, hF2, hFe⟩
  · exact absurd (h.le_of_alternatingGroup_le_centClosure L hLc hn hn6 φ hA) hLM
  rw [Fintype.card_fin] at hn11
  obtain ⟨a, b, hab, hFab⟩ := Finset.card_eq_two.1 hF2
  have hQfix : ∀ q ∈ pCoreOf 2 M, ∀ x, x ≠ a → x ≠ b → θ q x = x := by
    set N : Subgroup G :=
      (fixingSubgroup (Perm (Fin n)) ({x | x ∉ fixE (E.map θ)} : Set (Fin n))).comap θ with hN
    have hQN : pCoreOf 2 M ≤ N := h.le_of_forall_centralizer_le fun e he he1 q hq hqe => by
      rw [hN, Subgroup.mem_comap, mem_fixingSubgroup_iff]
      intro x hx
      have hθe1 : θ e ≠ 1 := fun h1 => he1 (hfaith e he h1)
      have hsupp : (θ e).supportᶜ = fixE (E.map θ) := hFe (θ e) (Subgroup.mem_map_of_mem θ he) hθe1
      have hxs : x ∈ (θ e).support := by
        by_contra hxs
        apply hx
        rw [← hsupp]
        exact Finset.mem_compl.2 hxs
      exact fix_of_normalized h.prime h.odd (hpow e he) (hRe2 e) (hReσ e)
        (h.normalizes_centralizer_qbar L hn hn6 φ he he1) (hmemR e q hq hqe) hxs
    intro q hq x hxa hxb
    have hxF : x ∉ fixE (E.map θ) := by
      rw [hFab]
      simp [hxa, hxb]
    exact (mem_fixingSubgroup_iff _).1 (Subgroup.mem_comap.1 (hQN hq)) x
      (show x ∈ ({x | x ∉ fixE (E.map θ)} : Set (Fin n)) from hxF)
  have hQswap : ∀ q ∈ pCoreOf 2 M, θ q = 1 ∨ θ q = swap a b := fun q hq =>
    eq_one_or_eq_swap hab (hQfix q hq)
  have hθt : θ q₀ = swap a b := (hQswap q₀ hq₀).resolve_left hθq₀
  have hZ : center ↥L = ⊥ := h.center_eq_bot L hL.1.1 (by omega) φ
  have hZG : ∀ z, z ∈ centerOf L → z = 1 := by
    intro z hz
    rw [centerOf_eq, hZ, Subgroup.map_bot, Subgroup.mem_bot] at hz
    exact hz
  have hact1 : ∀ g : G, θ g = 1 → ∀ y ∈ L, g * y * g⁻¹ = y := by
    intro g hg y hy
    exact mul_inv_eq_one.1 (hZG _ ((theta_eq_one_iff L hn hn6 φ g).1 hg y hy))
  refine ⟨hp3, hn11, hZ, q₀, hq₀, ?_, ?_, ?_⟩
  · subst hn11
    exact inducesTransposition_of_theta L hZ hn hn6 φ ⟨a, b, hab, rfl⟩ hθt
  · by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    refine hθq₀ ((theta_eq_one_iff L hn hn6 φ q₀).2 fun y hy => ?_)
    rw [hcon y hy, mul_inv_cancel]
    exact (centerOf L).one_mem
  · intro q hq
    rcases hQswap q hq with h1 | h1
    · exact Or.inl (hact1 q h1)
    · right
      intro y hy
      have h2 : θ (q₀⁻¹ * q) = 1 := by
        rw [map_mul, map_inv, h1, hθt, inv_mul_cancel]
      have h3 := hact1 _ h2 y hy
      calc q * y * q⁻¹ = q₀ * ((q₀⁻¹ * q) * y * (q₀⁻¹ * q)⁻¹) * q₀⁻¹ := by group
        _ = q₀ * y * q₀⁻¹ := by rw [h3]

theorem k36Concl_of_alt (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) (hLM : L ⊔ M = ⊤) {n : ℕ} (φ : ↥L ⧸ center ↥L ≃* alternatingGroup (Fin n))
    (hn : 5 ≤ n) (h3 : 13 ≤ n → twoLocalPrimeRank 3 G ≤ 3) : K36Concl M p := by
  obtain ⟨hp3, -, -, t, ht, hind, ⟨y₀, hy₀, hty₀⟩, hall⟩ := h.alt_conclusion hL hne φ hn h3
  have hone : ∀ q ∈ pCoreOf 2 M, (∀ y ∈ L, q * y * q⁻¹ = y) → q = 1 := by
    intro q hq hqL
    have hmem : q ∈ pCoreOf 2 M ⊓ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_inf.2 ⟨hq, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      calc y * q = (q * y * q⁻¹) * q := by rw [hqL y hy]
        _ = q * y := by group
    rw [h.inf_centralizer_eq_bot hLM] at hmem
    exact Subgroup.mem_bot.1 hmem
  have ht2 : t ^ 2 = 1 := by
    have htt : t * t ∈ pCoreOf 2 M := (pCoreOf 2 M).mul_mem ht ht
    rw [pow_two]
    refine hone _ htt ((hall _ htt).resolve_right fun hcon => hty₀ ?_)
    have h1 := hcon y₀ hy₀
    calc t * y₀ * t⁻¹ = t⁻¹ * ((t * t) * y₀ * (t * t)⁻¹) * t := by group
      _ = t⁻¹ * (t * y₀ * t⁻¹) * t := by rw [h1]
      _ = y₀ := by group
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hty₀ (by group)
  refine ⟨hp3, t, orderOf_eq_prime ht2 ht1, le_antisymm (fun q hq => ?_) ((Subgroup.zpowers_le).2 ht),
    L, inferInstance, hLM, Or.inr ⟨⟨hind.choose_spec.choose⟩, hind⟩⟩
  rcases hall q hq with h1 | h1
  · rw [hone q hq h1]
    exact (Subgroup.zpowers t).one_mem
  · have hq' : t⁻¹ * q ∈ pCoreOf 2 M := (pCoreOf 2 M).mul_mem ((pCoreOf 2 M).inv_mem ht) hq
    have h2 : t⁻¹ * q = 1 := hone _ hq' fun y hy => by
      calc t⁻¹ * q * y * (t⁻¹ * q)⁻¹ = t⁻¹ * (q * y * q⁻¹) * t := by group
        _ = t⁻¹ * (t * y * t⁻¹) * t := by rw [h1 y hy]
        _ = y := by group
    rw [inv_mul_eq_one] at h2
    rw [← h2]
    exact Subgroup.mem_zpowers t

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
