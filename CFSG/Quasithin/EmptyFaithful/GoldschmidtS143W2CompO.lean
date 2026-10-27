module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompN

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

theorem sq_mem_center_of_conj {L : Type} [Group L] {Gc : Type} [Group Gc] (ρ : Gc →* MulAut L)
    {ž : Gc} (hsq : ž * ž = 1) {l : L} (hl : ρ ž = MulAut.conj l) : l * l ∈ Subgroup.center L := by
  have h1 : MulAut.conj (l * l) = 1 := by
    rw [map_mul, ← hl, ← map_mul, hsq, map_one]
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  have h2 := congrArg (fun φ : MulAut L => φ y) h1
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  calc y * (l * l) = ((l * l) * y * (l * l)⁻¹) * (l * l) := by rw [h2]
    _ = (l * l) * y := by group

section Final

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}
  {L : Subgroup G}

theorem exists_witness_of_inducesInner (h : Ctx T M g A t d x) {ρ : GwQ d x →* MulAut ↥L}
    (hLN : Gw d x ≤ Subgroup.normalizer (L : Set G))
    (hρ : ∀ k : ↥(Gw d x), ρ (gwMk d x k) = Insp7.actOn hLN k)
    (hind : ∃ l ∈ L, ∀ y ∈ L, (d * d)⁻¹ * y * (d * d) = l⁻¹ * y * l) :
    ∃ l : ↥L, l * l ∈ Subgroup.center ↥L ∧ ρ (zQ h) = MulAut.conj l := by
  obtain ⟨l, hl, hly⟩ := hind
  have hzinv : (d * d)⁻¹ = d * d := inv_eq_of_mul_eq_one_right h.z_sq
  have hconj : ρ (zQ h) = MulAut.conj (⟨l⁻¹, L.inv_mem hl⟩ : ↥L) := by
    rw [show zQ h = gwMk d x ⟨d * d, h.z_mem_Gw⟩ from rfl, hρ]
    ext y
    rw [Insp7.actOn_apply_coe]
    have key := hly y y.2
    rw [hzinv] at key
    change (d * d) * (y : G) * (d * d)⁻¹ = l⁻¹ * (y : G) * (l⁻¹)⁻¹
    rw [hzinv, inv_inv]
    exact key
  refine ⟨⟨l⁻¹, L.inv_mem hl⟩, ?_, hconj⟩
  refine sq_mem_center_of_conj ρ ?_ hconj
  rw [show zQ h = gwMk d x ⟨d * d, h.z_mem_Gw⟩ from rfl, ← map_mul]
  have : (⟨d * d, h.z_mem_Gw⟩ * ⟨d * d, h.z_mem_Gw⟩ : ↥(Gw d x)) = 1 := Subtype.ext h.z_sq
  rw [this, map_one]

theorem inspData_of_normal (hlist : Lemma115_3_List) (h : Ctx T M g A t d x)
    (hf : LocalFacts T d x) (hL : IsComponentIn L (Gw d x))
    (hLN : Gw d x ≤ Subgroup.normalizer (L : Set G)) : InspData ↥L := by
  refine ⟨isQuasisimple_of_isComponentIn hL, ?_⟩
  obtain ⟨ρ, hρ, hin⟩ := inspInput_Gw h hf hL hLN
  have hsimple := h.c.hyp.simple
  have hcases : Lemma115Cases L (d * d) :=
    hlist G hsimple h.c.hyp.nonabelian (qtkeCore_of_cat h.c.hyp.nonabelian h.c.hyp.qtke)
      (Gw d x) (Tw T d x) (mcOf T) (d * d) (lemma115Hyp_Gw h) L hL
  refine ⟨GwQ d x, inferInstance, inferInstance, ρ, zQ h, ShatGw T d x, KhatGw T d x, hin, ?_⟩
  rcases hcases with hA | hB | hC | hD | hE | hF
  · exact Or.inr ⟨Or.inl ⟨hA.1, hA.2.1⟩, exists_witness_of_inducesInner h hLN hρ hA.2.2⟩
  · exact Or.inr ⟨Or.inr (Or.inl ⟨hB.1, hB.2.1, hB.2.2.1⟩),
      exists_witness_of_inducesInner h hLN hρ hB.2.2.2⟩
  · obtain ⟨φ', σ, hcard, -, -⟩ := hC
    exact Or.inl ⟨6, Or.inl rfl, ⟨φ'⟩, hcard⟩
  · obtain ⟨φ', σ, hcard, -, -⟩ := hD
    exact Or.inl ⟨7, Or.inr rfl, ⟨φ'⟩, hcard⟩
  · exact Or.inr ⟨Or.inr (Or.inr (Or.inl hE.1)), exists_witness_of_inducesInner h hLN hρ hE.2⟩
  · obtain ⟨l, hl, hly, -⟩ := hF.2
    exact Or.inr ⟨Or.inr (Or.inr (Or.inr hF.1)),
      exists_witness_of_inducesInner h hLN hρ ⟨l, hl, hly⟩⟩

end Final

end InspW2

end S143

end CFSG.Quasithin
