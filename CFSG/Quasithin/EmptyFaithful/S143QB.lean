module

public import CFSG.Quasithin.EmptyFaithful.S143QA
public import CFSG.Quasithin.EmptyFaithful.S143ND

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Tight
  CFSG.QuasithinUnique.BenderBranch CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

section Cyclic

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)

omit [Finite G] c hD in
theorem dd_facts (hd4 : orderOf d = 4) : (d * d) * (d * d) = 1 ∧ d * d ≠ 1 := by
  have h1 : d ^ 4 = 1 := by rw [← hd4]; exact pow_orderOf_eq_one d
  have h2 : d ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hd4] at this
    omega
  refine ⟨?_, by rwa [← pow_two]⟩
  calc (d * d) * (d * d) = d ^ 4 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    _ = 1 := h1

include c hD hd4 in
theorem sq_mem_omegaOneCenter : d * d ∈ quasithinOmegaOneCenter T := by
  obtain ⟨hdd4, hdd1⟩ := dd_facts hd4
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    have h2 := c.h1281.card_omegaOneCenter
    have : Nontrivial ↥(quasithinOmegaOneCenter T) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [h2]; norm_num)
    obtain ⟨w, hw⟩ := exists_ne (1 : ↥(quasithinOmegaOneCenter T))
    exact ⟨w, w.2, fun h => hw (Subtype.ext h)⟩
  have hz₀D : z₀ ∈ Subgroup.zpowers d := hD ▸ Z_le_dOf c hz₀
  have hz₀2 : z₀ * z₀ = 1 := by
    have := sq_eq_one_of_mem_omegaOneCenter T hz₀
    rwa [pow_two] at this
  rcases mem_zpowers_four rfl hdd4 hz₀D with h | h | h | h
  · exact absurd h hz₀1
  · exfalso
    rw [h] at hz₀2
    exact hdd1 hz₀2
  · rw [← h]; exact hz₀
  · exfalso
    rw [h] at hz₀2
    apply hdd1
    calc d * d = d * d * ((d * d) * (d * d)) := by rw [hdd4, mul_one]
      _ = (d * ((d * d))) * (d * (d * d)) := by group
      _ = 1 := hz₀2

include c hD hd4 in
theorem mem_normalizer_zpowers_of_comm {x : G} (hx : x * (d * d) * x⁻¹ = d * d) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  have hz := sq_mem_omegaOneCenter c hD hd4
  have hz1 := (dd_facts hd4).2
  have hxz : x * (d * d) = (d * d) * x := by
    calc x * (d * d) = (x * (d * d) * x⁻¹) * x := by group
      _ = (d * d) * x := by rw [hx]
  have hxH : x ∈ mcOf T := c.mem_mcOf_of_comm hz hz1 hxz
  have hdD : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : y ∈ dOf T M := hD ▸ hy
    exact hD ▸ c.conj_mem_dOf hxH this
  · intro hy
    have hy' : x * y * x⁻¹ ∈ dOf T M := hD ▸ hy
    have := c.conj_mem_dOf ((mcOf T).inv_mem hxH) hy'
    have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rw [e] at this
    exact hD ▸ this

end Cyclic

section XDef

variable {G : Type} [Group G]

@[expose] def Xgen (T M : Subgroup G) : Subgroup G := Wgen (Delta ⊤ (dOf T M) T)

end XDef

section Xsec

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)

theorem dOf_le_T_of_counter (c : Counter T M g) : dOf T M ≤ T :=
  (inf_le_left : dOf T M ≤ qOf T).trans (qOf_le_T_of_hyp c.h1281)

include c hD hd4 in
theorem setup_dOf : Tight.Setup (dOf T M) ⊤ (dOf T M) T := by
  obtain ⟨hdd4, hdd1⟩ := dd_facts hd4
  have hDT : dOf T M ≤ T := dOf_le_T_of_counter c
  have hD2 : IsPGroup 2 ↥(dOf T M) := c.hyp.sylow.1.to_le hDT
  refine ⟨?_, ⟨le_inf le_top le_rfl, hD2, ?_⟩, ?_, c.hyp.sylow.1, le_top, hDT⟩
  · rw [hD]
    exact tightlyEmbedded_zpowers_of_sq rfl hdd1 hdd4
      (fun x hx => mem_normalizer_zpowers_of_comm c hD hd4 hx)
  · rw [Subgroup.subgroupOf_eq_top.mpr inf_le_right, Subgroup.index_top]
    norm_num
  · intro h
    apply hdd1
    have : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
    rw [h, Subgroup.mem_bot] at this
    rw [this, mul_one]

include c hD hd4 in
theorem Xgen_comm : ∀ x ∈ Xgen T M, ∀ y ∈ Xgen T M, x * y = y * x := by
  have hS := setup_dOf c hD hd4
  have hΦ : ∃ y ∈ dOf T M, y ^ 2 ≠ 1 :=
    ⟨d, hD ▸ Subgroup.mem_zpowers d, by rw [pow_two]; exact (dd_facts hd4).2⟩
  refine Wgen_comm (hS.delta_commute hΦ) ?_
  intro R hR a ha b hb
  obtain ⟨⟨h, -, rfl⟩, -⟩ := hR
  rw [BenderBranch.mem_conjugate_iff] at ha hb
  have ha' : h * a * h⁻¹ ∈ Subgroup.zpowers d := hD ▸ ha
  have hb' : h * b * h⁻¹ ∈ Subgroup.zpowers d := hD ▸ hb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha'
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hb'
  have hcomm : (h * a * h⁻¹) * (h * b * h⁻¹) = (h * b * h⁻¹) * (h * a * h⁻¹) := by
    rw [← hk, ← hl]
    exact (Commute.zpow_zpow_self d k l).eq
  calc a * b = h⁻¹ * ((h * a * h⁻¹) * (h * b * h⁻¹)) * h := by group
    _ = h⁻¹ * ((h * b * h⁻¹) * (h * a * h⁻¹)) * h := by rw [hcomm]
    _ = b * a := by group

omit [Finite G] in
theorem Xgen_le_T : Xgen T M ≤ T := Wgen_le_of_le fun _ hR => hR.2

end Xsec

section LPart

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)

include c in
theorem dOf_le_pCoreOf_LT : dOf T M ≤ pCoreOf 2 (yOfL22 T M ⊔ T) := by
  rw [← c.h1281.centralizer]
  intro x hx
  refine ⟨Subgroup.mem_sup_right (dOf_le_T_of_counter c hx),
    Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  exact Subgroup.mem_centralizer_iff.mp hx.2 v (Hyp1281Two.VZ_le_uOfL22 T M hv)

include c in
theorem pCoreOf_LT_le_T : pCoreOf 2 (yOfL22 T M ⊔ T) ≤ T :=
  EscapingLocal.pCoreOf_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo c.hyp.sylow le_sup_right)

omit [Finite G] in
theorem conj_mem_pCoreOf_LT {L T' : Subgroup G} {l w : G} (hl : l ∈ L ⊔ T')
    (hw : l * w * l⁻¹ ∈ pCoreOf 2 (L ⊔ T')) : w ∈ pCoreOf 2 (L ⊔ T') :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hl) w).mpr hw

include c in
theorem conjSubgroup_dOf_le_T {l : G} (hl : l ∈ yOfL22 T M) : conjSubgroup (dOf T M) l ≤ T := by
  intro w hw
  have h1 : l * w * l⁻¹ ∈ dOf T M := mem_conjSubgroup_iff.mp hw
  exact pCoreOf_LT_le_T c (conj_mem_pCoreOf_LT (Subgroup.mem_sup_left hl) (dOf_le_pCoreOf_LT c h1))

include c in
theorem conjSubgroup_dOf_mem_delta {l : G} (hl : l ∈ yOfL22 T M) :
    conjSubgroup (dOf T M) l ∈ Delta ⊤ (dOf T M) T :=
  ⟨⟨l, trivial, rfl⟩, conjSubgroup_dOf_le_T c hl⟩

include c in
theorem dOf_mem_delta : dOf T M ∈ Delta ⊤ (dOf T M) T :=
  ⟨⟨1, trivial, (conjugate_one _).symm⟩, dOf_le_T_of_counter c⟩

include c in
theorem VZ_le_Xgen : VZ T M ≤ Xgen T M := by
  have hg := c.goodElt
  obtain ⟨z, a, hzZ, hz1, ha, haV, haZ, hzz, haa, hza, hga, hgza, hall⟩ :=
    exists_three_cycle c.h1281 hg
  have hgL : g ∈ yOfL22 T M := hg.mem
  have hg' : g⁻¹ ∈ yOfL22 T M := (yOfL22 T M).inv_mem hgL
  have hg'' : g⁻¹ * g⁻¹ ∈ yOfL22 T M := (yOfL22 T M).mul_mem hg' hg'
  have hzD : z ∈ dOf T M := Z_le_dOf c hzZ
  intro w hw
  rcases hall w hw with rfl | rfl | rfl | rfl
  · exact (Xgen T M).one_mem
  · exact le_Wgen (dOf_mem_delta c) hzD
  · refine le_Wgen (conjSubgroup_dOf_mem_delta c hg') ?_
    rw [mem_conjSubgroup_iff]
    have : g⁻¹ * w * g⁻¹⁻¹ = z := by rw [ha]; group
    rw [this]; exact hzD
  · refine le_Wgen (conjSubgroup_dOf_mem_delta c hg'') ?_
    rw [mem_conjSubgroup_iff]
    have h1 : g⁻¹ * (z * a) * g = a := by
      calc g⁻¹ * (z * a) * g = g⁻¹ * (g * a * g⁻¹) * g := by rw [hga]
        _ = a := by group
    have : g⁻¹ * g⁻¹ * (z * a) * (g⁻¹ * g⁻¹)⁻¹ = z := by
      calc g⁻¹ * g⁻¹ * (z * a) * (g⁻¹ * g⁻¹)⁻¹ = g⁻¹ * (g⁻¹ * (z * a) * g) * g := by
            rw [mul_inv_rev, inv_inv]; simp only [mul_assoc]
        _ = g⁻¹ * a * g := by rw [h1]
        _ = z := by rw [ha]; group
    rw [this]; exact hzD

include c hD hd4 in
theorem Xgen_le_pCoreOf_LT : Xgen T M ≤ pCoreOf 2 (yOfL22 T M ⊔ T) := by
  rw [← c.h1281.centralizer]
  intro x hx
  refine ⟨Subgroup.mem_sup_right (Xgen_le_T hx), Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  exact Xgen_comm c hD hd4 v (VZ_le_Xgen c hv) x hx

include c hD hd4 in
theorem LT_le_normalizer_Xgen : yOfL22 T M ⊔ T ≤ Subgroup.normalizer (Xgen T M : Set G) := by
  intro l hl
  have hle : conjSubgroup (Xgen T M) l ≤ T := by
    intro w hw
    have h1 : l * w * l⁻¹ ∈ Xgen T M := mem_conjSubgroup_iff.mp hw
    exact pCoreOf_LT_le_T c (conj_mem_pCoreOf_LT hl (Xgen_le_pCoreOf_LT c hD hd4 h1))
  have heq : conjSubgroup (Xgen T M) l = Xgen T M := isWeaklyClosedIn_Wgen_delta (dOf T M) T l hle
  exact conjugate_eq_iff_mem_normalizer.mp heq

include c hD hd4 in
theorem normalizer_Xgen_le : Subgroup.normalizer (Xgen T M : Set G) ≤ M := by
  have hU := c.h1281.unique
  have hX2 : IsPGroup 2 ↥(Xgen T M) := c.hyp.sylow.1.to_le Xgen_le_T
  have hd1 : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have hX1 : Xgen T M ≠ ⊥ := by
    intro h
    have : d ∈ Xgen T M := le_Wgen (dOf_mem_delta c) hd1
    rw [h, Subgroup.mem_bot] at this
    apply (dd_facts hd4).2
    rw [this, mul_one]
  have hpC : pCoreOf 2 (Subgroup.normalizer (Xgen T M : Set G)) ≠ ⊥ := by
    intro h
    have hle : Xgen T M ≤ pCoreOf 2 (Subgroup.normalizer (Xgen T M : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hX2
    exact hX1 (le_bot_iff.mp (h ▸ hle))
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hpC
  have h1 : M' = M := hU.2 M' ⟨hM'.1, (LT_le_normalizer_Xgen c hD hd4).trans hM'.2⟩
  exact h1 ▸ hM'.2

end LPart

section Fusion

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)

include c in
theorem conj_dOf_iff {x w : G} (hx : x ∈ mcOf T) : x * w * x⁻¹ ∈ dOf T M ↔ w ∈ dOf T M := by
  constructor
  · intro h
    have := c.conj_mem_dOf ((mcOf T).inv_mem hx) h
    have e : x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ = w := by group
    rwa [e] at this
  · exact c.conj_mem_dOf hx

include c hD hd4 in
theorem delta_eq_conj {R : Subgroup G} (hR : R ∈ Delta ⊤ (dOf T M) T) :
    ∃ l ∈ yOfL22 T M, R = conjSubgroup (dOf T M) l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo c.hyp.sylow
  have hR' := hR
  obtain ⟨⟨h, -, hRh⟩, hRT⟩ := hR'
  have hRX : R ≤ Xgen T M := le_Wgen hR
  have hDX : dOf T M ≤ Xgen T M := le_Wgen (dOf_mem_delta c)
  have hXS : Xgen T M ≤ (S : Subgroup G) := by rw [hS]; exact Xgen_le_T
  have hweak : IsWeaklyClosedIn (Xgen T M) (S : Subgroup G) := by
    rw [hS]; exact isWeaklyClosedIn_Wgen_delta (dOf T M) T
  have hfix : ∀ E : Subgroup G, E ≤ Xgen T M → ∀ w ∈ Xgen T M, conjSet (E : Set G) w = E := by
    intro E hE w hw
    rw [conjSet_eq_iff_mem_normalizer]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun e he => Xgen_comm c hD hd4 e (hE he) w hw)
  have hg : conjSet (dOf T M : Set G) h = (R : Set G) := by
    ext x
    rw [mem_conjSet_iff, hRh]
    exact (BenderBranch.mem_conjugate_iff).symm
  obtain ⟨n, hnN, hn⟩ := burnside_fusion_lemma S hXS hweak (hfix _ hDX) (hfix _ hRX) hg
  have hnM : n ∈ M := normalizer_Xgen_le c hD hd4 hnN
  obtain ⟨l, hlL, c', hc', hnl⟩ := c.h1281.exists_mul_eq ((M.inv_mem hnM) : n⁻¹ ∈ M)
  have hc'H : c' ∈ mcOf T := by
    have := hc'.2
    rw [normalizer_Z_eq_centralizer_of_hyp c.h1281] at this
    exact this
  have hn' : n = c'⁻¹ * l⁻¹ := by rw [← inv_inv n, hnl, mul_inv_rev]
  refine ⟨l⁻¹, (yOfL22 T M).inv_mem hlL, ?_⟩
  ext x
  have hRn : x ∈ R ↔ n * x * n⁻¹ ∈ dOf T M := by
    have := Set.ext_iff.mp hn x
    rw [mem_conjSet_iff] at this
    exact this.symm
  rw [hRn, mem_conjSubgroup_iff, hn']
  have e : c'⁻¹ * l⁻¹ * x * (c'⁻¹ * l⁻¹)⁻¹ = c'⁻¹ * (l⁻¹ * x * l⁻¹⁻¹) * c'⁻¹⁻¹ := by group
  rw [e]
  exact conj_dOf_iff c ((mcOf T).inv_mem hc'H)

end Fusion

end S143

end CFSG.Quasithin
