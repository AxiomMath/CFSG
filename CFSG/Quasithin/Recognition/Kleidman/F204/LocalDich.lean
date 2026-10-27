module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalZ
public import CFSG.Quasithin.EmptyFaithful.S152He9W
public import CFSG.Quasithin.Recognition.Kleidman.F204.GeoBase2
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPhi

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
theorem exists_pow_sq_mem (Q : Subgroup G) {n : ℕ} :
    ∀ {t : G}, t ∉ Q → t ^ 2 ^ n ∈ Q → ∃ j : ℕ, t ^ j ∉ Q ∧ t ^ j * t ^ j ∈ Q := by
  induction n with
  | zero => intro t ht hn; exact absurd (by simpa using hn) ht
  | succ n ih =>
    intro t ht hn
    by_cases h2 : t * t ∈ Q
    · exact ⟨1, by simpa using ht, by simpa using h2⟩
    · have e : ∀ j : ℕ, (t * t) ^ j = t ^ (2 * j) := fun j => by rw [← pow_two, ← pow_mul]
      obtain ⟨j, hj1, hj2⟩ := ih h2 (by rw [e, ← pow_succ']; exact hn)
      exact ⟨2 * j, by rwa [e] at hj1, by rwa [e] at hj2⟩

omit [Finite G] in
theorem pow_mem_of_pow_eq_one {t : G} {n : ℕ} (hn : t ^ 2 ^ n = 1) (Q : Subgroup G) :
    t ^ 2 ^ n ∈ Q := by
  rw [hn]; exact Q.one_mem

section Basic

variable (F : Frame L1 L2 S D X)

include F

theorem Qv_le_centralizer_Zv (δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)) :
    Qv δ ≤ Subgroup.centralizer (Zv δ : Set G) := by
  intro q hq z hz
  have h := (Amal.of_frame F).Zv_le_centerOf_Qv δ hz
  exact (Subgroup.mem_centralizer_iff.mp h.2 q hq).symm

omit F in
theorem omega_le_Zv (δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)) {T : Subgroup G}
    (hT : IsSylowTwoOf T (stab δ)) : quasithinOmegaOneCenter T ≤ Zv δ := by
  rw [Zv_eq_conjClosure hT]; exact le_conjClosure _ _

theorem Zv_eq_omega_of_central (δ : Geo (P1 L1 L2 S) (P2 L1 L2 S))
    (hc : stab δ ≤ Subgroup.centralizer (Zv δ : Set G)) {T : Subgroup G}
    (hT : IsSylowTwoOf T (stab δ)) : Zv δ = quasithinOmegaOneCenter T := by
  refine le_antisymm (fun z hz => ?_) (omega_le_Zv δ hT)
  have hA := Amal.of_frame F
  have hzQ : z ∈ Qv δ := hA.Zv_le_Qv δ hz
  have hzT : z ∈ T := isSylowTwoOf_pCoreOf_le hT hzQ
  have hz2 : z ^ 2 = 1 := (hA.isElemAbelian_Zv δ).2 z hz
  refine Subgroup.subset_closure ⟨⟨hzT, ?_⟩, hz2⟩
  intro t ht
  exact (Subgroup.mem_centralizer_iff.mp (hc (hT.1 ht)) z hz).symm

theorem inf_centralizer_eq_Qv (δ : Geo (P1 L1 L2 S) (P2 L1 L2 S))
    (hc : stab δ ⊓ Subgroup.centralizer (Zv δ : Set G) ≤ Qv δ) {T : Subgroup G}
    (hT : IsSylowTwoOf T (stab δ)) : T ⊓ Subgroup.centralizer (Zv δ : Set G) = Qv δ := by
  apply le_antisymm
  · exact fun t ht => hc ⟨hT.1 ht.1, ht.2⟩
  · exact fun q hq => ⟨isSylowTwoOf_pCoreOf_le hT hq, Qv_le_centralizer_Zv F δ hq⟩

theorem conj_mem_inf_centralizer (δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)) {k c : G} (hk : k ∈ stab δ)
    (hc : c ∈ stab δ ⊓ Subgroup.centralizer (Zv δ : Set G)) :
    k * c * k⁻¹ ∈ stab δ ⊓ Subgroup.centralizer (Zv δ : Set G) := by
  refine ⟨(stab δ).mul_mem ((stab δ).mul_mem hk hc.1) ((stab δ).inv_mem hk), ?_⟩
  intro z hz
  have hN := (Amal.of_frame F).stab_le_normalizer_Zv δ
  have hz' : k⁻¹ * z * k ∈ Zv δ := by
    have := (Subgroup.mem_normalizer_iff.mp (hN ((stab δ).inv_mem hk)) z).mp hz
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hz'
  calc z * (k * c * k⁻¹) = k * ((k⁻¹ * z * k) * c) * k⁻¹ := by group
    _ = k * (c * (k⁻¹ * z * k)) * k⁻¹ := by rw [h1]
    _ = k * c * k⁻¹ * z := by group

end Basic

theorem dichotomy_true (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = true) :
    (∀ T, IsSylowTwoOf T (stab δ) → Zv δ = quasithinOmegaOneCenter T) ∨
      (∀ T, IsSylowTwoOf T (stab δ) → T ⊓ Subgroup.centralizer (Zv δ : Set G) = Qv δ) := by
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_stab F hδ
  set C : Subgroup G := stab δ ⊓ Subgroup.centralizer (Zv δ : Set G) with hC
  have hnorm : (C.subgroupOf (stab δ)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_inf_centralizer F δ g.2 hn
  have hmapn : (Subgroup.map φ (C.subgroupOf (stab δ))).Normal := hnorm.map φ hφs
  have := hmapn
  have hQC : Qv δ ≤ C := fun q hq =>
    ⟨(pCoreOf_le 2 (stab δ)) hq, Qv_le_centralizer_Zv F δ hq⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.map φ (C.subgroupOf (stab δ))) with h | h
  · right
    refine fun T hT => inf_centralizer_eq_Qv F δ (fun c hc => ?_) hT
    have h1 : (⟨c, hc.1⟩ : ↥(stab δ)) ∈ C.subgroupOf (stab δ) := hc
    have h2 : φ ⟨c, hc.1⟩ ∈ Subgroup.map φ (C.subgroupOf (stab δ)) := ⟨_, h1, rfl⟩
    rw [h, Subgroup.mem_bot] at h2
    have h3 : (⟨c, hc.1⟩ : ↥(stab δ)) ∈ φ.ker := h2
    rw [hφk, Subgroup.mem_subgroupOf] at h3
    exact h3
  · left
    refine fun T hT => Zv_eq_omega_of_central F δ (fun g hg => ?_) hT
    have h2 : φ ⟨g, hg⟩ ∈ Subgroup.map φ (C.subgroupOf (stab δ)) := by rw [h]; trivial
    obtain ⟨c, hc, hcg⟩ := h2
    have hker : (c⁻¹ * ⟨g, hg⟩ : ↥(stab δ)) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcg, inv_mul_cancel]
    rw [hφk, Subgroup.mem_subgroupOf] at hker
    have hcC : (c : G) ∈ C := hc
    have hq : ((c⁻¹ * ⟨g, hg⟩ : ↥(stab δ)) : G) ∈ C := hQC hker
    have : g = (c : G) * ((c⁻¹ * ⟨g, hg⟩ : ↥(stab δ)) : G) := by simp
    rw [this]
    exact (C.mul_mem hcC hq).2

theorem five_centralizes_Zv_of_two (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) {t : G} (ht : t ∈ stab δ) {n : ℕ} (htn : t ^ 2 ^ n = 1)
    (htC : t ∈ Subgroup.centralizer (Zv δ : Set G)) (htQ : t ∉ Qv δ) :
    ∀ x ∈ stab δ, x ^ 5 = 1 → x ∈ Subgroup.centralizer (Zv δ : Set G) := by
  intro x hx hx5
  have hA := Amal.of_frame F
  obtain ⟨j, hj1, hj2⟩ := exists_pow_sq_mem (Qv δ) htQ (pow_mem_of_pow_eq_one htn _)
  obtain ⟨h, hh1, hh2, hhx⟩ := exists_conj_stab_false_X F hδ hx hx5
  set u := t ^ j with hu
  have huS : u ∈ stab δ := (stab δ).pow_mem ht j
  have huC : u ∈ Subgroup.centralizer (Zv δ : Set G) := Subgroup.pow_mem _ htC j
  set u₁ := h * u * h⁻¹ with hu₁
  have hu₁P : u₁ ∈ P1 L1 L2 S := by rw [← hh1]; exact mem_conjSub_of_mem' huS
  have hu₁Q : u₁ ∉ Q1 L1 L2 S := by
    intro hm
    rw [← hh2, hu₁, mem_conjSub] at hm
    apply hj1
    have e : h⁻¹ * (h * u * h⁻¹) * h = u := by group
    rwa [e] at hm
  have hu₁2 : u₁ * u₁ ∈ Q1 L1 L2 S := by
    rw [← hh2]
    have e : u₁ * u₁ = h * (u * u) * h⁻¹ := by rw [hu₁]; group
    rw [e]
    exact mem_conjSub_of_mem' hj2
  obtain ⟨q, hq, hinv⟩ := inv_of_involution_P1 F hu₁P hu₁2 hu₁Q hhx
  set x₀ := h⁻¹ * (h * x * h⁻¹) * h with hx₀
  have hx₀e : x₀ = x := by rw [hx₀]; group
  set q₀ := h⁻¹ * q * h with hq₀
  have hq₀Q : q₀ ∈ Qv δ := by
    have : q ∈ conjSub h (Qv δ) := by rw [hh2]; exact hq
    exact mem_conjSub.mp this
  have hinv₀ : u * x * u⁻¹ = x⁻¹ * q₀ := by
    have h1 : h⁻¹ * (u₁ * (h * x * h⁻¹) * u₁⁻¹) * h = u * x * u⁻¹ := by rw [hu₁]; group
    have h2 : h⁻¹ * ((h * x * h⁻¹)⁻¹ * q) * h = x⁻¹ * q₀ := by rw [hq₀]; group
    rw [← h1, ← h2, hinv]
  have hxN : x ∈ Subgroup.normalizer (Zv δ : Set G) := hA.stab_le_normalizer_Zv δ hx
  have huN : u ∈ Subgroup.normalizer (Zv δ : Set G) := hA.stab_le_normalizer_Zv δ huS
  have hV2 : ∀ a ∈ Zv δ, a * a = 1 := fun a ha => by
    rw [← pow_two]; exact (hA.isElemAbelian_Zv δ).2 a ha
  have hq₀c := Qv_le_centralizer_Zv F δ hq₀Q
  have huu : u * u ∈ Subgroup.centralizer (Zv δ : Set G) := (Subgroup.centralizer _).mul_mem huC huC
  have hidx : ((Zv δ) ⊓ Subgroup.centralizer {u}).relIndex (Zv δ) ≤ 2 := by
    have : (Zv δ) ⊓ Subgroup.centralizer {u} = Zv δ := by
      apply inf_eq_left.mpr
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp huC z hz
    rw [this, Subgroup.relIndex_self]
    norm_num
  exact FA5.centralizes_of_inverted_transvection hV2 hxN huN hq₀c hx5 huu hinv₀ hidx

theorem dichotomy_false (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) :
    (∀ T, IsSylowTwoOf T (stab δ) → Zv δ = quasithinOmegaOneCenter T) ∨
      (∀ T, IsSylowTwoOf T (stab δ) → T ⊓ Subgroup.centralizer (Zv δ : Set G) = Qv δ) := by
  by_cases h5 : ∀ x ∈ stab δ, x ^ 5 = 1 → x ∈ Subgroup.centralizer (Zv δ : Set G)
  · exact Or.inl fun T hT => Zv_eq_omega_of_five F hδ h5 hT
  · right
    intro T hT
    apply le_antisymm
    · intro t ht
      by_contra htQ
      apply h5
      obtain ⟨n, hn⟩ := hT.2.1 ⟨t, ht.1⟩
      have htn : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      exact five_centralizes_Zv_of_two F hδ (hT.1 ht.1) htn ht.2 htQ
    · exact fun q hq => ⟨isSylowTwoOf_pCoreOf_le hT hq, Qv_le_centralizer_Zv F δ hq⟩

theorem dichotomy (F : Frame L1 L2 S D X) (δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)) :
    (∀ T, IsSylowTwoOf T (stab δ) → Zv δ = quasithinOmegaOneCenter T) ∨
      (∀ T, IsSylowTwoOf T (stab δ) → T ⊓ Subgroup.centralizer (Zv δ : Set G) = Qv δ) := by
  cases hv : vtype δ
  · exact dichotomy_false F hv
  · exact dichotomy_true F hv

end CFSG.Quasithin.Kleidman.F204
