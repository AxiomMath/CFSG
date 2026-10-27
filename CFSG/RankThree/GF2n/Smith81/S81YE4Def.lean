module

public import CFSG.RankThree.GF2n.Smith81.S81YE5Def
public import CFSG.RankThree.GF2n.Smith81.S81D6Roots
public import CFSG.RankThree.GF2n.Smith81.S81D6Fe3c

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE4

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenE5


@[expose] noncomputable def LG (K : Type) [Field K] : Subgroup (G7 K) :=
  (Lam K).comap (e7Data_valid.minGroup K).subtype

variable {K : Type} [Field K]

theorem mem_LG {g : G7 K} : g ∈ LG K ↔ (g : (Module.End K (V K))ˣ) ∈ Lam K := Iff.rfl

@[expose] noncomputable def IsPureL (v : V K) : Prop :=
  ∃ g ∈ LG K, ∃ c : K, c ≠ 0 ∧ v = c • act7 g (Finsupp.single (a0 : Fin e7Data.d) 1)

@[expose] noncomputable def lamToG7 [CharP K 2] (l : ↥(Lam K)) : G7 K := ⟨(l : (Module.End K (V K))ˣ), Lam_le_E l.2⟩

theorem lamToG7_mem [CharP K 2] (l : ↥(Lam K)) : lamToG7 l ∈ LG K := l.2

@[expose] noncomputable def act4 [CharP K 2] (l : ↥(Lam K)) : W K ≃ₗ[K] W K :=
  vAut0 K (resV0 K l)

theorem emb_act4 [CharP K 2] (l : ↥(Lam K)) (w : W K) :
    emb K (act4 l w) = act7 (lamToG7 l) (emb K w) := by
  rw [act7_apply]
  exact resV0_induces l w

theorem act4_mul [CharP K 2] (l l' : ↥(Lam K)) : act4 (l * l') = act4 l * act4 l' := by
  unfold act4
  rw [map_mul, map_mul]

theorem act4_one [CharP K 2] : act4 (1 : ↥(Lam K)) = 1 := by
  unfold act4
  rw [map_one, map_one]

theorem act4_inv [CharP K 2] (l : ↥(Lam K)) : act4 l⁻¹ = (act4 l)⁻¹ := by
  unfold act4
  rw [map_inv, map_inv]

theorem mem_EAut0_iff_act4 [CharP K 2] {r : W K ≃ₗ[K] W K} :
    r ∈ EAut0 K ↔ ∃ l : ↥(Lam K), act4 l = r := by
  unfold EAut0
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, hgr⟩
    obtain ⟨l, rfl⟩ := mem_LamW_iff.1 hg
    exact ⟨l, hgr⟩
  · rintro ⟨l, rfl⟩
    exact ⟨resV0 K l, mem_LamW_iff.2 ⟨l, rfl⟩, rfl⟩

theorem emb_p0 : emb K (p0 K) = Finsupp.single (a0 : Fin e7Data.d) 1 := by
  unfold p0
  exact emb_single a0 1

@[expose] def IsRt4 (r : W K ≃ₗ[K] W K) : Prop := IsRootEltW ((vAut0 K).symm r)

theorem isRt4_iff [CharP K 2] {r : W K ≃ₗ[K] W K} :
    IsRt4 r ↔ ∃ l : ↥(Lam K), IsRootEltL K (lamToG7 l) ∧ act4 l = r := by
  constructor
  · intro hr
    unfold IsRt4 IsRootEltW at hr
    obtain ⟨l, hl, β, hβ, c, hc, hI⟩ := hr
    obtain ⟨L, hL⟩ : ∃ L : ↥(Lam K),
        (L : (Module.End K (V K))ˣ) = l * e7Data_valid.xu K β c * l⁻¹ :=
      ⟨⟨l * e7Data_valid.xu K β c * l⁻¹, mul_mem (mul_mem hl (xu_mem_Lam hβ c)) (inv_mem hl)⟩,
        rfl⟩
    have hI' : Induces (resV0 K L) (l * e7Data_valid.xu K β c * l⁻¹) := by
      rw [← hL]
      exact resV0_induces L
    have hres : (vAut0 K).symm r = resV0 K L := Induces.unique hI hI'
    refine ⟨L, ?_, ?_⟩
    · unfold IsRootEltL
      exact ⟨⟨l, Lam_le_E hl⟩, β, c, hl, hβ, hc, Subtype.ext hL⟩
    · unfold act4
      rw [← hres]
      exact (vAut0 K).apply_symm_apply r
  · rintro ⟨l, hroot, rfl⟩
    unfold IsRootEltL at hroot
    obtain ⟨h, β, c, hh, hβ, hc, hg⟩ := hroot
    have hu : ((l : ↥(Lam K)) : (Module.End K (V K))ˣ) =
        (h : (Module.End K (V K))ˣ) * e7Data_valid.xu K β c * (h : (Module.End K (V K))ˣ)⁻¹ :=
      Subtype.ext_iff.1 hg
    have hI : Induces (resV0 K l)
        ((h : (Module.End K (V K))ˣ) * e7Data_valid.xu K β c * (h : (Module.End K (V K))ˣ)⁻¹) := by
      rw [← hu]
      exact resV0_induces l
    have e : (vAut0 K).symm (act4 l) = resV0 K l := by
      unfold act4
      exact (vAut0 K).symm_apply_apply _
    unfold IsRt4 IsRootEltW
    rw [e]
    exact ⟨(h : (Module.End K (V K))ˣ), hh, β, hβ, c, hc, hI⟩

theorem isRt4_mul_self [CharP K 2] {r : W K ≃ₗ[K] W K} (hr : IsRt4 r) : r * r = 1 := by
  unfold IsRt4 at hr
  have h1 : (vAut0 K).symm r * (vAut0 K).symm r = 1 := IsRootEltW.mul_self hr
  have h2 : vAut0 K ((vAut0 K).symm r * (vAut0 K).symm r) = vAut0 K 1 := by
    rw [h1]
  rw [map_mul, map_one, (vAut0 K).apply_symm_apply] at h2
  exact h2

theorem isPureL_emb [CharP K 2] {p : W K} (hp : IsPurePt (EAut0 K) (p0 K) p) :
    IsPureL (emb K p) := by
  unfold IsPurePt at hp
  obtain ⟨g, hg, c, hc, hpc⟩ := hp
  obtain ⟨l, rfl⟩ := mem_EAut0_iff_act4.1 hg
  unfold IsPureL
  refine ⟨lamToG7 l, lamToG7_mem l, c, hc, ?_⟩
  rw [hpc, map_smul, emb_act4, emb_p0]

theorem isPurePt_of_isPureL [CharP K 2] {p : W K} (hp : IsPureL (emb K p)) :
    IsPurePt (EAut0 K) (p0 K) p := by
  unfold IsPureL at hp
  obtain ⟨g, hg, c, hc, hpc⟩ := hp
  have hgL : (g : (Module.End K (V K))ˣ) ∈ Lam K := mem_LG.1 hg
  obtain ⟨l, hlg⟩ : ∃ l : ↥(Lam K), lamToG7 l = g :=
    ⟨⟨(g : (Module.End K (V K))ˣ), hgL⟩, rfl⟩
  unfold IsPurePt
  refine ⟨act4 l, mem_EAut0_iff_act4.2 ⟨l, rfl⟩, c, hc, ?_⟩
  apply emb_injective
  rw [map_smul, emb_act4, emb_p0, hlg]
  exact hpc

end CFSG.RankThree.GF2n.Smith81.RootGenE4
