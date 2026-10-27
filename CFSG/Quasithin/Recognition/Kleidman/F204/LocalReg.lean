module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPhi
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalA5b
public import CFSG.Quasithin.EmptyFaithful.S152He9W
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalQ

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem exists_klein_phi (F : Frame L1 L2 S D X) {φ : ↥(P2 L1 L2 S) →* Alt5}
    (hφs : Function.Surjective φ) (hφk : ∀ p : ↥(P2 L1 L2 S), φ p = 1 ↔ (p : G) ∈ Q2 L1 L2 S) :
    ∃ T : Subgroup Alt5, Nat.card T = 4 ∧
      (∀ k ∈ T, ∃ q : ↥(P2 L1 L2 S), (q : G) ∈ Q1 L1 L2 S ∧ φ q = k) ∧
      ∀ p : ↥(P2 L1 L2 S), φ p ∈ Subgroup.normalizer (T : Set Alt5) ↔ (p : G) ∈ bigB L1 L2 S := by
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hBP : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
  set S' : Subgroup ↥(P2 L1 L2 S) := S.subgroupOf (P2 L1 L2 S) with hS'
  set T : Subgroup Alt5 := S'.map φ with hT
  have hpS' : IsPGroup 2 S' :=
    F.sylow_P2.2.1.comap_of_injective (P2 L1 L2 S).subtype (P2 L1 L2 S).subtype_injective
  have hTp : IsPGroup 2 T := hpS'.map φ
  have hTodd : ¬ 2 ∣ T.index := fun h =>
    F.sylow_P2.2.2 (h.trans (Subgroup.index_map_dvd S' hφs))
  have hT4 : Nat.card T = 4 := card_eq_four_of_sylow hTp hTodd
  have hlift : ∀ k ∈ T, ∃ q : ↥(P2 L1 L2 S), (q : G) ∈ Q1 L1 L2 S ∧ φ q = k := by
    rintro k ⟨s, hs, rfl⟩
    have hsS : (s : G) ∈ S := hs
    have hsQ : (s : G) ∈ Q2 L1 L2 S ⊔ Q1 L1 L2 S := by
      rw [sup_comm, Q1_sup_Q2 F]; exact hsS
    have hN : Q1 L1 L2 S ≤ Subgroup.normalizer ((Q2 L1 L2 S : Subgroup G) : Set G) := fun q hq =>
      P2_le_normalizer_Q2 L1 L2 S (hBP (hSB (F.Q1_le_S hq)))
    obtain ⟨a, ha, b, hb, hab⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hN).mp hsQ
    have haP : a ∈ P2 L1 L2 S := pCoreOf_le 2 (P2 L1 L2 S) ha
    have hbP : b ∈ P2 L1 L2 S := hBP (hSB (F.Q1_le_S hb))
    refine ⟨⟨b, hbP⟩, hb, ?_⟩
    have h1 : s = ⟨a, haP⟩ * ⟨b, hbP⟩ := Subtype.ext hab
    rw [h1, map_mul, (hφk ⟨a, haP⟩).mpr ha, one_mul]
  have hBN : ∀ p : ↥(P2 L1 L2 S), (p : G) ∈ bigB L1 L2 S →
      φ p ∈ Subgroup.normalizer (T : Set Alt5) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    have hpN : ∀ r : ↥(P2 L1 L2 S), (r : G) ∈ bigB L1 L2 S → ∀ s : ↥(P2 L1 L2 S), (s : G) ∈ S →
        (r * s * r⁻¹ : ↥(P2 L1 L2 S)) ∈ S' := by
      intro r hr s hs
      have := (Subgroup.mem_normalizer_iff.mp (F.B_le_normalizer_S hr) s).mp hs
      exact this
    intro t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨_, hpN p hp s hs, by simp⟩
    · rintro ⟨s, hs, hst⟩
      have hp' : ((p⁻¹ : ↥(P2 L1 L2 S)) : G) ∈ bigB L1 L2 S := (bigB L1 L2 S).inv_mem hp
      refine ⟨p⁻¹ * s * p, ?_, ?_⟩
      · have := hpN p⁻¹ hp' s hs
        simpa using this
      · rw [map_mul, map_mul, map_inv, hst]
        group
  refine ⟨T, hT4, hlift, fun p => ⟨fun hpN => ?_, fun hp => hBN p hp⟩⟩
  set C : Subgroup ↥(P2 L1 L2 S) := (Subgroup.normalizer (T : Set Alt5)).comap φ with hC
  set B' : Subgroup ↥(P2 L1 L2 S) := (bigB L1 L2 S).subgroupOf (P2 L1 L2 S) with hB'
  have hB'C : B' ≤ C := fun r hr => hBN r hr
  have hB'idx : B'.index = 5 := F.pair.relIndex_bigB_right
  have hCtop : C ≠ ⊤ := by
    intro htop
    have hNtop : Subgroup.normalizer (T : Set Alt5) = ⊤ := by
      rw [eq_top_iff]
      intro a _
      obtain ⟨r, rfl⟩ := hφs a
      have : r ∈ C := by rw [htop]; trivial
      exact this
    have hTn : T.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with h | h
    · rw [h, Subgroup.card_bot] at hT4; omega
    · rw [h] at hT4
      have : Nat.card (⊤ : Subgroup Alt5) = Nat.card Alt5 := Subgroup.card_top
      rw [this, a5_card] at hT4; omega
  have hdvd : C.index ∣ 5 := hB'idx ▸ Subgroup.index_dvd_of_le hB'C
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h1
  · exact absurd (Subgroup.index_eq_one.mp h1) hCtop
  · have hm := Subgroup.relIndex_mul_index hB'C
    rw [h1, hB'idx] at hm
    have : B'.relIndex C = 1 := by omega
    exact (Subgroup.relIndex_eq_one.mp this) (show p ∈ C from hpN)

theorem Q1_trans_P2 (F : Frame L1 L2 S D X) {p p' : G} (hp : p ∈ P2 L1 L2 S)
    (hp' : p' ∈ P2 L1 L2 S) (hpB : p ∉ bigB L1 L2 S) (hp'B : p' ∉ bigB L1 L2 S) :
    ∃ q ∈ Q1 L1 L2 S, p'⁻¹ * q * p ∈ bigB L1 L2 S := by
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_P2 F
  obtain ⟨T, hT4, hlift, hN⟩ := exists_klein_phi F hφs hφk
  obtain ⟨k, hk, hkN⟩ := alt5_klein_trans hT4 (x := φ ⟨p, hp⟩) (y := φ ⟨p', hp'⟩)
    (fun h => hpB ((hN _).mp h)) (fun h => hp'B ((hN _).mp h))
  obtain ⟨q, hq, hqk⟩ := hlift k hk
  refine ⟨q, hq, ?_⟩
  have : φ (⟨p', hp'⟩⁻¹ * q * ⟨p, hp⟩) ∈ Subgroup.normalizer (T : Set Alt5) := by
    rw [map_mul, map_mul, map_inv, hqk]; exact hkN
  exact (hN _).mp this

end CFSG.Quasithin.Kleidman.F204
