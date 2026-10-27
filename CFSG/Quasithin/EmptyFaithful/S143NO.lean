module

public import CFSG.Quasithin.EmptyFaithful.S143NN
public import CFSG.Quasithin.EmptyFaithful.S143NA2
public import CFSG.Quasithin.EmptyFaithful.S143NJ

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace S143

open A6Model

@[expose] def Lemma14320Inspect : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.QuasithinUnique.QTKECore G →
    ∀ (S M : Subgroup G) (z d : G), d ≠ 1 → d * d = 1 →
      pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) = Subgroup.zpowers d →
      ∀ h : Lemma115Hyp (Subgroup.centralizer ({d} : Set G)) S M z,
        ∀ L : Subgroup G, IsComponentIn L (Subgroup.centralizer ({d} : Set G)) → z ∈ L →
          Lemma115Cases L z →
          ∀ (Gc : Type) [Group Gc] (φ : ↥(Subgroup.centralizer ({d} : Set G)) →* Gc),
            Function.Surjective φ →
            φ.ker = (Subgroup.zpowers d).subgroupOf (Subgroup.centralizer ({d} : Set G)) →
            ∀ P : Subgroup Gc, P ≤ Subgroup.centralizer ({φ ⟨z, h.z_mem_H⟩} : Set Gc) →
              P.relIndex (Subgroup.centralizer ({φ ⟨z, h.z_mem_H⟩} : Set Gc)) ≤ 2 →
                ¬ ExtQ8SqS3S3 ↥P

theorem normal_zpowers_subgroupOf_centralizer {G : Type*} [Group G] (d : G) :
    ((Subgroup.zpowers d).subgroupOf (Subgroup.centralizer ({d} : Set G))).Normal := by
  have hle : Subgroup.zpowers d ≤ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun h' hh' => by
      rw [Set.mem_singleton_iff] at hh'; subst hh'; rfl)
  refine (Subgroup.normal_subgroupOf_iff hle).mpr fun h k hh hk => ?_
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hc : Commute k d := (Subgroup.mem_centralizer_iff.mp hk d rfl).symm
  have : k * d ^ m * k⁻¹ = d ^ m := by
    have := (hc.zpow_right m).eq
    calc k * d ^ m * k⁻¹ = (d ^ m * k) * k⁻¹ := by rw [← this]
      _ = d ^ m := by group
  rw [this]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers d) m

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4} (hM : KModel hS cm y)
  {Vl Vr : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)} (hP : Conf6Plus cm Vl Vr s)
  (hVl : ∀ σ ∈ Vl, ∃ u ∈ uOfL22 T M, mm cm (matOf6 σ) = mm (cmat z a r r1 u) cm)
  (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)
  {δ : G} (hδD : δ ∈ dOf T M) (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))
  (hδA : δ ∉ c.Ac hrW hrV hr2)
  (hemb : ∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X))
  (hnc : ∀ x' : G, x' * z * x'⁻¹ ≠ δ) (hnc' : ∀ x' : G, x' * z * x'⁻¹ ≠ z * δ)

include hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb hnc hnc' in
theorem lemma115Hyp_gd :
    Lemma115Hyp (Subgroup.centralizer ({δ} : Set G)) (tdOf T δ) (mcOf T) z := by
  have hQ := c.hyp.qtke
  have hz := hS.z_mem
  have hz1 := hS.z_ne
  have hδ2 : δ * δ = 1 := Gamma_sq hS htT htRQ hM hC1 hδ
  have hδ1 : δ ≠ 1 := fun e => hδA (e ▸ (c.Ac hrW hrV hr2).one_mem)
  have hzT : z ∈ T := (quasithinOmegaOneCenter_le_center T hz).1
  have hzcT : z ∈ Subgroup.centralizer (T : Set G) := (quasithinOmegaOneCenter_le_center T hz).2
  have hSyl := isSylowTwoOf_tdOf_gd hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb hnc hnc'
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers δ) := by
    have hord : orderOf δ = 2 := orderOf_eq_prime (by rw [← pow_two] at hδ2; exact hδ2) hδ1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
  exact lemma116 hQ.2.1 hzp (by rw [Ne, Subgroup.zpowers_eq_bot]; exact hδ1)
    (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun h' hh' => by
        rw [Set.mem_singleton_iff] at hh'; subst hh'; rfl))
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers δ))))
    (centralizer_singleton_le_normalizer_zpowers δ) hSyl
    (isSylowTwoOf_of_quasithinIsSylowTwo c.hyp.sylow le_top) inf_le_left hzT hzcT hz1
    (by have := sq_eq_one_of_mem_omegaOneCenter T hz; exact this) c.hyp.mc_max
    (fun w hw => Subgroup.mem_centralizer_iff.mpr fun u hu => by
      rcases c.mem_Z_cases hz hz1 hu with h | h
      · rw [h]; simp
      · rw [h]; exact (Subgroup.mem_centralizer_iff.mp hw z rfl))

end Main

theorem lemma_14_3_20_of_inputs
    (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hlist : Lemma115_3_List)
    (hins : Lemma14320Inspect) : Lemma14320 := by
  intro G _ _ T M g A t c c18 c19
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq c18.b
  obtain ⟨x, z, a, r1, hS⟩ := c.exists_setup hrW hrV hr2 c18.a
  have htT := c18.b.t_mem
  have htRQ := c18.b.t_nmem
  obtain ⟨y, cm, Vl, Vr, s, hM, hP, hVl, hVr⟩ := hS.exists_KModel3 htT htRQ
  have hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1 := by
    intro γ hγ
    have h : γ ∈ Subgroup.centralizer (kOf T M (c.Ac hrW hrV hr2) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr hγ
    rw [c19.b.centralizer_K] at h
    exact Subgroup.mem_bot.mp h
  have hNAK := c19.b.normalizer_A
  have hNA : Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) =
      kOf T M (c.Ac hrW hrV hr2) ⊔ dOf T M := hNAK.trans c19.b.normalizer_K
  by_contra hne
  have hAC : c.Ac hrW hrV hr2 ≤ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) := fun a' ha' =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => hS.basis.comm w hw a' ha'
  have hΓ : c.Ac hrW hrV hr2 < Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
    lt_of_le_of_ne hAC (fun h => hne h.symm)
  obtain ⟨δ, hδD, hδ, hδA⟩ := exists_delta hS hM hP.conf htT htRQ hNA hΓ
  obtain ⟨p, hps, hcoc⟩ := exists_unit_cocyc hS htT htRQ hM hP hVl hC1 hδD hδ hδA
  obtain ⟨y₅, hy₅, hy₅o⟩ := exists_order_five_kd hS htT htRQ hM hδD hδ hδA hcoc
  obtain ⟨k, hkK, hk⟩ := exists_conj_zdelta hS htT htRQ hM hP hVl hC1 hδD hδ hδA
  have hnc : ∀ x' : G, x' * z * x'⁻¹ ≠ δ :=
    c.not_conj_of_order_five hS.z_mem hS.z_ne hy₅o
      (Subgroup.mem_centralizer_iff.mp hy₅.2 δ rfl).symm
  have hnc' : ∀ x' : G, x' * z * x'⁻¹ ≠ z * δ := by
    intro x' hx'
    apply hnc (k⁻¹ * x')
    calc (k⁻¹ * x') * z * (k⁻¹ * x')⁻¹ = k⁻¹ * (x' * z * x'⁻¹) * k := by group
      _ = k⁻¹ * (z * δ) * k := by rw [hx']
      _ = k⁻¹ * (k * δ * k⁻¹) * k := by rw [hk]
      _ = δ := by group
  have hemb := c19.b.D_le_D8
  obtain ⟨L, hLcomp, hzL, -, hcases⟩ := exists_component_Ld hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA
    hps hcoc hy₅ hy₅o hemb c18.c c18.a.rq_index c18.b.r_eq_AAt hNAK hNA hnc hnc' c18.b.A_elem
    h37 h39 hlist
  have hHyp := lemma115Hyp_gd hS htT htRQ hM hP hVl hC1 hδD hδ hδA hemb hnc hnc'
  have hOeq := pCoreOf_gd_eq hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc hy₅ hy₅o hemb c18.c
    c18.a.rq_index c18.b.r_eq_AAt hNAK hNA hnc hnc'
  have hδ1 : δ ≠ 1 := fun e => hδA (e ▸ (c.Ac hrW hrV hr2).one_mem)
  have hδ2 : δ * δ = 1 := Gamma_sq hS htT htRQ hM hC1 hδ
  have hsimple := c.hyp.simple
  have hnormal := normal_zpowers_subgroupOf_centralizer δ
  obtain ⟨P, hP1, hP2, hext⟩ := exists_pattern_gd hS htT htRQ hM hP hVl hVr hC1 hδD hδ hδA hps hcoc
    hemb c18.a.rq_index c18.b.r_eq_AAt hnc hnc' c19.a.q_eq hHyp.z_mem_H
    (QuotientGroup.mk' ((Subgroup.zpowers δ).subgroupOf (Subgroup.centralizer ({δ} : Set G))))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  exact hins G hsimple c.hyp.nonabelian (qtkeCore_of_cat c.hyp.nonabelian c.hyp.qtke)
    (tdOf T δ) (mcOf T) z δ hδ1 hδ2 hOeq hHyp L hLcomp hzL hcases _
    (QuotientGroup.mk' ((Subgroup.zpowers δ).subgroupOf (Subgroup.centralizer ({δ} : Set G))))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) P hP1 hP2 hext

end S143

end CFSG.Quasithin
