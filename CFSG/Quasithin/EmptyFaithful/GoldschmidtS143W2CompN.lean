module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompM
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompH

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

abbrev ShatGw {G : Type} [Group G] (T : Subgroup G) (d x : G) : Subgroup (GwQ d x) :=
  ((Tw T d x).subgroupOf (Gw d x)).map (gwMk d x)

abbrev KhatGw {G : Type} [Group G] (T : Subgroup G) (d x : G) : Subgroup (GwQ d x) :=
  ((K0 T d x).subgroupOf (Gw d x)).map (gwMk d x)

section Input

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}
  {L : Subgroup G}

theorem inspInput_Gw (h : Ctx T M g A t d x) (hf : LocalFacts T d x)
    (hL : IsComponentIn L (Gw d x)) (hLN : Gw d x ≤ Subgroup.normalizer (L : Set G)) :
    ∃ ρ : GwQ d x →* MulAut ↥L, (∀ k : ↥(Gw d x), ρ (gwMk d x k) = Insp7.actOn hLN k) ∧
      InspInput ρ (zQ h) (ShatGw T d x) (KhatGw T d x) := by
  have hker : ∀ k : ↥(Gw d x), (k : G) ∈ Subgroup.centralizer (L : Set G) ↔
      k ∈ CFSG.pCore 2 ↥(Gw d x) := by
    intro k
    rw [mem_pCore_iff, ← inf_centralizer_eq_pCoreOf h hf hL hLN]
    exact ⟨fun hk => ⟨k.2, hk⟩, fun hk => hk.2⟩
  obtain ⟨ρ, hρinj, hρφ⟩ := exists_embedding_of_ker hLN hker
  have hρφ' : ∀ k : ↥(Gw d x), ρ (gwMk d x k) = Insp7.actOn hLN k := hρφ
  refine ⟨ρ, hρφ', ?_⟩
  have hcentz := centralizer_zQ h hf.wp1
  have hzq : zQ h = gwMk d x ⟨d * d, h.z_mem_Gw⟩ := rfl
  have hKle : KhatGw T d x ≤ Subgroup.centralizer ({zQ h} : Set (GwQ d x)) := by
    rw [hcentz]
    exact Subgroup.map_mono fun k hk =>
      Subgroup.mem_subgroupOf.mpr (h.K0_le_Cw (Subgroup.mem_subgroupOf.mp hk))
  have hKker : (K0 T d x).subgroupOf (Gw d x) ⊓ (gwMk d x).ker = ⊥ := by
    rw [eq_bot_iff]
    rintro k ⟨hk, hkk⟩
    have hkP : (k : G) ∈ pCoreOf 2 (Gw d x) := (mem_pCore_iff k).mp (by
      rwa [QuotientGroup.ker_mk'] at hkk)
    have : (k : G) ∈ pCoreOf 2 (Gw d x) ⊓ K0 T d x := ⟨hkP, Subgroup.mem_subgroupOf.mp hk⟩
    rw [hf.wp1.P_inf_K0, Subgroup.mem_bot] at this
    exact Subtype.ext this
  obtain ⟨eK⟩ := exists_mulEquiv_map _ (gwMk d x) hKker
  have hSyl := h.hSyl
  have hS2 : IsPGroup 2 ((Tw T d x).subgroupOf (Gw d x)) :=
    hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSyl.1).symm
  have hcard1 := card_centralizer_zQ_mul h hf
  have hcard2 := card_Shat_mul h hf
  have hpos : 0 < Nat.card ↥(pCoreOf 2 (Gw d x)) := Nat.card_pos
  refine
    { inj := hρinj
      inn := ?_
      sq := ?_
      ne := ?_
      sylow := ⟨hS2.map _, fun h2 => hSyl.2.2
        (h2.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))⟩
      cent := ?_
      K_le := hKle
      K_norm := ?_
      K_shape := isZ4StarSL23_of_mulEquiv
        ((Subgroup.subgroupOfEquivOfLe inf_le_right).symm.trans eK) h.hO
      ž_mem := ⟨⟨d * d, h.z_mem_Gw⟩, Subgroup.mem_subgroupOf.mpr h.z_mem_K0, rfl⟩
      ž_cent := fun k hk => (Subgroup.mem_centralizer_singleton_iff.mp (hKle hk))
      card_C := ?_
      card_S := ?_
      E := exists_E_data h hf.wp1 }
  · intro l
    refine ⟨gwMk d x ⟨l, hL.1 l.2⟩, ?_⟩
    rw [hρφ']
    ext y
    rw [Insp7.actOn_apply_coe]
    simp
  · rw [hzq, ← map_mul]
    have : (⟨d * d, h.z_mem_Gw⟩ * ⟨d * d, h.z_mem_Gw⟩ : ↥(Gw d x)) = 1 := Subtype.ext h.z_sq
    rw [this, map_one]
  · intro h1
    exact hf.wp1.z_not_mem_P ((mem_pCore_iff_mk_eq_one _).mp h1)
  · rintro _ ⟨s, hs, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [hzq, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.z_comm_Tw (Subgroup.mem_subgroupOf.mp hs))
  · rw [Subgroup.normal_subgroupOf_iff hKle]
    intro k q hk hq
    rw [hcentz] at hq
    obtain ⟨c, hc, rfl⟩ := hq
    obtain ⟨k0, hk0, rfl⟩ := hk
    refine ⟨c * k0 * c⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact (Subgroup.normal_subgroupOf_iff h.K0_le_Cw).mp hf.wp0.K0_normal _ _
        (Subgroup.mem_subgroupOf.mp hk0) (Subgroup.mem_subgroupOf.mp hc)
    · simp only [map_mul, map_inv]
  · apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hcard1, mul_assoc, hcard2]; norm_num
  · rcases card_P_cases h hf with hP | hP <;> rw [hP] at hcard2 <;> norm_num at hcard2 ⊢ <;> omega

end Input

end InspW2

end S143

end CFSG.Quasithin
