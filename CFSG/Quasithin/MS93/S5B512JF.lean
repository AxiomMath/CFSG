module

public import CFSG.Quasithin.MS93.S5AGeo
public import CFSG.Quasithin.MS93.S5BJ
public import CFSG.Quasithin.MS93.S5BTv

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S5B

section LinAlg

variable {F : Type} [Field F]

private theorem eq_one_of_pow_two_pow' [CharP F 2] {c : F} {n : ℕ} (h : c ^ 2 ^ n = 1) :
    c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (c - 1) ^ 2 ^ n = 0 := by rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by positivity)).mp h1)

private theorem exists_pow_mulVec' {g : MSP.Sp4 F} {S : Submodule F (MSP.V4 F)}
    (hS : ∀ x ∈ S, MSP.mat g *ᵥ x ∈ S) {w s : MSP.V4 F} {μ : F}
    (hs : s ∈ S) (hw : MSP.mat g *ᵥ w = s + μ • w) (m : ℕ) :
    ∃ s' ∈ S, MSP.mat (g ^ m) *ᵥ w = s' + μ ^ m • w := by
  induction m with
  | zero => exact ⟨0, S.zero_mem, by simp [MSP.mat_one]⟩
  | succ m ih =>
    obtain ⟨s', hs', e⟩ := ih
    refine ⟨MSP.mat g *ᵥ s' + μ ^ m • s, S.add_mem (hS s' hs') (S.smul_mem _ hs), ?_⟩
    rw [pow_succ' g m, MSP.mat_mul_mulVec, e, Matrix.mulVec_add, Matrix.mulVec_smul, hw,
      smul_add, smul_smul, pow_succ μ m, add_assoc]

theorem sub_mem_of_pow_two_pow_V4 [CharP F 2] {g : MSP.Sp4 F} {n : ℕ} (hg : g ^ 2 ^ n = 1)
    {S : Submodule F (MSP.V4 F)} (hS : ∀ x ∈ S, MSP.mat g *ᵥ x ∈ S) {w : MSP.V4 F}
    (hw : MSP.mat g *ᵥ w ∈ S ⊔ F ∙ w) : MSP.mat g *ᵥ w - w ∈ S := by
  by_cases hwS : w ∈ S
  · exact S.sub_mem (hS w hwS) hwS
  obtain ⟨s, hs, y, hy, e⟩ := Submodule.mem_sup.mp hw
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨s', hs', e'⟩ := exists_pow_mulVec' hS hs e.symm (2 ^ n)
  rw [hg, MSP.mat_one, Matrix.one_mulVec] at e'
  have hμ : μ ^ 2 ^ n = 1 := by
    by_contra hne
    apply hwS
    have h1 : (1 - μ ^ 2 ^ n) • w = s' := by
      rw [sub_smul, one_smul, eq_sub_of_add_eq e'.symm]
    have h2 : (1 - μ ^ 2 ^ n) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h3 : (1 - μ ^ 2 ^ n) • w ∈ S := by rw [h1]; exact hs'
    have := S.smul_mem (1 - μ ^ 2 ^ n)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ h2, one_smul] at this
  rw [← e, eq_one_of_pow_two_pow' hμ, one_smul, add_sub_cancel_right]
  exact hs

theorem sub_mem_of_le_of_finrank_le [CharP F 2] {g : MSP.Sp4 F} {n : ℕ} (hg : g ^ 2 ^ n = 1)
    {U W : Submodule F (MSP.V4 F)} (hUW : U ≤ W)
    (hfin : Module.finrank F W ≤ Module.finrank F U + 1)
    (hU : ∀ x ∈ U, MSP.mat g *ᵥ x ∈ U) (hW : ∀ x ∈ W, MSP.mat g *ᵥ x ∈ W)
    {w : MSP.V4 F} (hw : w ∈ W) : MSP.mat g *ᵥ w - w ∈ U := by
  by_cases hwU : w ∈ U
  · exact U.sub_mem (hU w hwU) hwU
  have hle : U ⊔ F ∙ w ≤ W := sup_le hUW ((Submodule.span_singleton_le_iff_mem _ _).2 hw)
  have hlt : U < U ⊔ F ∙ w := lt_of_le_of_ne le_sup_left fun he =>
    hwU (he ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have hsup : U ⊔ F ∙ w = W := Submodule.eq_of_le_of_finrank_le hle (by omega)
  exact sub_mem_of_pow_two_pow_V4 hg hU (hsup ▸ hW w hw)

theorem exists_mulVec_ne {g : MSP.Sp4 F} (hg : g ≠ 1) : ∃ v : MSP.V4 F, MSP.mat g *ᵥ v ≠ v := by
  by_contra hcon
  push Not at hcon
  exact hg (MSP.ext_mulVec fun v => by rw [hcon v, MSP.mat_one, Matrix.one_mulVec])

theorem exists_ne_one_of_ne_bot {E : Subgroup (MSP.Sp4 F)} (hE : E ≠ ⊥) : ∃ z ∈ E, z ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact hE (eq_bot_iff.2 fun z hz => Subgroup.mem_bot.2 (hcon z hz))

theorem eq_one_of_mem_fixer_of_mem_stab {l₀ l : Submodule F (MSP.V4 F)} (hl₀ : MSP.IsLine l₀)
    (hl : MSP.IsLine l) (hll : l₀ ⊓ l = ⊥) {z : MSP.Sp4 F} (hz₀ : z ∈ MSP.fixer l₀)
    (hz : z ∈ MSP.stab l) : z = 1 := by
  have hsup : l₀ ⊔ l = ⊤ := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq l₀ l
    rw [hll, finrank_bot, hl₀.1, hl.1] at h1
    exact Submodule.eq_top_of_finrank_eq (by simp; omega)
  refine MSP.ext_mulVec fun v => ?_
  rw [MSP.mat_one, Matrix.one_mulVec]
  have hv : v ∈ l₀ ⊔ l := hsup ▸ Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
  rw [Matrix.mulVec_add, hz₀ x hx]
  congr 1
  have h1 : MSP.mat z *ᵥ y - y ∈ l₀ := MSP.commSp_qLine_le hl₀ (MSP.sub_mem_commSp hz₀ y)
  have h2 : MSP.mat z *ᵥ y - y ∈ l := l.sub_mem (MSP.mulVec_mem_of_mem_stab hz hy) hy
  have h3 : MSP.mat z *ᵥ y - y ∈ l₀ ⊓ l := ⟨h1, h2⟩
  rw [hll] at h3
  exact sub_eq_zero.1 ((Submodule.mem_bot F).1 h3)

theorem fixSp_le_perp_of_le_qPoint {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p)
    {E : Subgroup (MSP.Sp4 F)} (hE : E ≤ MSP.qPoint p) (hE1 : E ≠ ⊥) :
    MSP.fixSp E ≤ MSP.perp p := by
  rw [fixSp_eq_perp_commSp]
  refine MSP.perp_antitone ?_
  obtain ⟨z, hzE, hz1⟩ := exists_ne_one_of_ne_bot hE1
  have hw : ∃ w : MSP.V4 F, MSP.mat z *ᵥ w - w ≠ 0 ∧ MSP.mat z *ᵥ w - w ∈ p := by
    by_cases hfix : ∀ v ∈ MSP.perp p, MSP.mat z *ᵥ v = v
    · obtain ⟨w, hw⟩ := exists_mulVec_ne hz1
      exact ⟨w, sub_ne_zero.2 hw,
        MSP.commSp_fixer_perp_le p (MSP.sub_mem_commSp (A := MSP.xPoint p) hfix w)⟩
    · push Not at hfix
      obtain ⟨v, hv, hzv⟩ := hfix
      exact ⟨v, sub_ne_zero.2 hzv, (hE hzE).2 v hv⟩
  obtain ⟨w, hw0, hwp⟩ := hw
  have hspan : F ∙ (MSP.mat z *ᵥ w - w) = p := by
    refine Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hwp) ?_
    rw [finrank_span_singleton hw0]
    exact hp.symm
  rw [← hspan]
  exact (Submodule.span_singleton_le_iff_mem _ _).2 (MSP.sub_mem_commSp hzE w)

theorem mem_stab_fixSp_of_mem_normalizer {E : Subgroup (MSP.Sp4 F)} {g : MSP.Sp4 F}
    (hg : g ∈ Subgroup.normalizer (E : Set (MSP.Sp4 F))) : g ∈ MSP.stab (MSP.fixSp E) := by
  rw [MSP.mem_stab_iff, ← MSP.fixSp_map_conj, MSP.mem_normalizer_iff_map_conj.1 hg]

theorem finrank_commSp_le_two {E : Subgroup (MSP.Sp4 F)}
    (hquad : MSP.commSp E ≤ MSP.fixSp E) :
    MSP.commSp E ≤ MSP.perp (MSP.commSp E) ∧ Module.finrank F (MSP.commSp E) ≤ 2 := by
  have hle : MSP.commSp E ≤ MSP.perp (MSP.commSp E) := (fixSp_eq_perp_commSp E) ▸ hquad
  refine ⟨hle, ?_⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := MSP.finrank_perp (MSP.commSp E)
  have h4 : Module.finrank F (MSP.V4 F) = 4 := by simp
  omega

theorem sub_mem_line_of_quad [CharP F 2] {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    {Z : Subgroup (MSP.Sp4 F)} (hZl : Z ≤ MSP.stab l) (hZ1 : Z ≠ ⊥)
    (hquad : MSP.commSp Z ≤ MSP.fixSp Z) {g : MSP.Sp4 F} {n : ℕ} (hg : g ^ 2 ^ n = 1)
    (hgl : g ∈ MSP.stab l) (hgZ : g ∈ Subgroup.normalizer (Z : Set (MSP.Sp4 F)))
    {v : MSP.V4 F} (hv : v ∈ MSP.fixSp Z) : MSP.mat g *ᵥ v - v ∈ l := by
  obtain ⟨hKK, hK2⟩ := finrank_commSp_le_two hquad
  set K := MSP.commSp Z with hK
  have hfixK : MSP.fixSp Z = MSP.perp K := fixSp_eq_perp_commSp Z
  have hgW : g ∈ MSP.stab (MSP.perp K) := hfixK ▸ mem_stab_fixSp_of_mem_normalizer hgZ
  have hgK : g ∈ MSP.stab K := (MSP.stab_perp K) ▸ hgW
  obtain ⟨z, hzZ, hz1⟩ := exists_ne_one_of_ne_bot hZ1
  have hZfix : Z ≤ MSP.fixer (MSP.perp K) := MSP.le_fixer_iff.2 hfixK.ge
  have h4 : Module.finrank F (MSP.V4 F) = 4 := by simp
  have hK0 : K ≠ ⊥ := by
    intro hbot
    apply hz1
    refine MSP.ext_mulVec fun w => ?_
    have := MSP.sub_mem_commSp hzZ w
    rw [← hK, hbot, Submodule.mem_bot, sub_eq_zero] at this
    rw [this, MSP.mat_one, Matrix.one_mulVec]
  have hKpos := S5.finrank_pos_of_ne_bot hK0
  have hvK : v ∈ MSP.perp K := hfixK ▸ hv
  have hgW' : ∀ x ∈ MSP.perp K, MSP.mat g *ᵥ x ∈ MSP.perp K :=
    fun x hx => MSP.mulVec_mem_of_mem_stab hgW hx
  have hgl' : ∀ x ∈ l, MSP.mat g *ᵥ x ∈ l := fun x hx => MSP.mulVec_mem_of_mem_stab hgl hx
  rcases Nat.lt_or_ge (Module.finrank F K) 2 with hK1 | hK2'
  ·
    have hP : MSP.IsPoint K := by
      change Module.finrank F K = 1
      omega
    have hPl : K ≤ l := le_of_mem_xPoint_stab hP hl (hZfix hzZ) (hZl hzZ) hz1
    have hlP : l ≤ MSP.perp K := by
      have := MSP.perp_antitone hPl
      rwa [hl.perp_eq] at this
    have hfin : Module.finrank F (MSP.perp K) ≤ Module.finrank F l + 1 := by
      have := MSP.finrank_perp K
      rw [hl.1]
      change Module.finrank F K = 1 at hP
      omega
    exact sub_mem_of_le_of_finrank_le hg hlP hfin hgl' hgW' hvK
  ·
    have hl₀ : MSP.IsLine K := ⟨by omega, fun x hx y hy => MSP.mem_perp.1 (hKK hy) x hx⟩
    have hKeq : MSP.perp K = K := hl₀.perp_eq
    rw [hKeq] at hvK hgW' hZfix
    by_cases hll : K ⊓ l = ⊥
    · exact absurd (eq_one_of_mem_fixer_of_mem_stab hl₀ hl hll (hZfix hzZ) (hZl hzZ)) hz1
    · have hPpos := S5.finrank_pos_of_ne_bot hll
      have hPle := Submodule.finrank_mono (inf_le_left : (K ⊓ l : Submodule F (MSP.V4 F)) ≤ K)
      have hgP : ∀ x ∈ K ⊓ l, MSP.mat g *ᵥ x ∈ K ⊓ l :=
        fun x hx => ⟨hgW' x hx.1, hgl' x hx.2⟩
      have hfin : Module.finrank F K ≤ Module.finrank F ↥(K ⊓ l) + 1 := by
        rw [hl₀.1]
        omega
      exact (inf_le_right : (K ⊓ l : Submodule F (MSP.V4 F)) ≤ l)
        (sub_mem_of_le_of_finrank_le hg inf_le_left hfin hgP hgW' hvK)

end LinAlg

section Base

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Fintype F] in
theorem vec_commutatorElement (h : PUHyp M T L)
    (c : MSP.NatCoord M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) a)
    {u m : G} (hu : u ∈ Uq M T L) (hm : m ∈ M) :
    ∃ hr : ⁅u, m⁆ ∈ Uq M T L,
      c.vec ⟨⁅u, m⁆, hr⟩ = -(MSP.mat (a ⟨m, hm⟩) *ᵥ c.vec ⟨u, hu⟩ - c.vec ⟨u, hu⟩) := by
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hconj : m * u * m⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn hm) u).1 hu
  have hcU : m * u * m⁻¹ * u⁻¹ ∈ Uq M T L := mul_mem hconj (inv_mem hu)
  have hrU : ⁅u, m⁆ ∈ Uq M T L := by
    have e : ⁅u, m⁆ = (m * u * m⁻¹ * u⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact inv_mem hcU
  refine ⟨hrU, ?_⟩
  have e : (⟨⁅u, m⁆, hrU⟩ : ↥(Uq M T L)) = (⟨_, hcU⟩ : ↥(Uq M T L))⁻¹ :=
    Subtype.ext (by
      show ⁅u, m⁆ = (m * u * m⁻¹ * u⁻¹)⁻¹
      rw [commutatorElement_def]
      group)
  rw [e, c.vec_inv, c.vec_commutator ⟨m, hm⟩ ⟨u, hu⟩ hconj]

omit [Fintype F] in
theorem commutator_le_centralizer_of_vec (h : PUHyp M T L)
    (hlift : ∀ m ∈ M, ∀ u ∈ Uq M T L, m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) →
      m * u * m⁻¹ = u)
    (c : MSP.NatCoord M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) a)
    {W : Submodule F (MSP.V4 F)} {Y A₀ J₀ : Subgroup G} (hY : Y ≤ Uq M T L) (hA₀M : A₀ ≤ M)
    (hvec : ∀ y (hy : y ∈ Y), ∀ m (hm : m ∈ A₀),
      MSP.mat (a ⟨m, hA₀M hm⟩) *ᵥ c.vec ⟨y, hY hy⟩ - c.vec ⟨y, hY hy⟩ ∈ W)
    (hJ₀M : J₀ ≤ M) (hJ₀W : (J₀.subgroupOf M).map a ≤ MSP.fixer W) :
    ⁅Y, A₀⁆ ≤ Subgroup.centralizer (J₀ : Set G) := by
  rw [Subgroup.commutator_le]
  intro y hy m hm
  obtain ⟨hr, hv⟩ := vec_commutatorElement h c (hY hy) (hA₀M hm)
  have hW : c.vec ⟨⁅y, m⁆, hr⟩ ∈ W := hv ▸ W.neg_mem (hvec y hy m hm)
  exact (mem_centralizer_iff_vec h hlift c hJ₀M ⟨_, hr⟩).2 (MSP.le_fixer_iff.1 hJ₀W hW)

omit [Finite G] [Fintype F] in
theorem imM_le_centralizer (hTM : T ≤ M) {X J₀ : Subgroup G} (hJ₀M : J₀ ≤ M)
    (hX : X ≤ Subgroup.centralizer (J₀ : Set G)) {J : Subgroup (puAmalgam hTM).Universal}
    (hJ : J ≤ imM hTM J₀) : imM hTM X ≤ Subgroup.centralizer (J : Set _) := by
  refine le_trans ?_ (Subgroup.centralizer_le hJ)
  have h1 := imM_inf_centralizer hTM X hJ₀M
  rw [inf_eq_left.2 hX] at h1
  rw [h1]
  exact inf_le_right

theorem map_ne_bot_of_not_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {E : Subgroup G}
    (hEM : E ≤ M) (hE2 : IsPGroup 2 E) (hEO : ¬ E ≤ pCoreOf 2 M) :
    (E.subgroupOf M).map a ≠ ⊥ := by
  intro hbot
  apply hEO
  intro e he
  have h1 : a ⟨e, hEM he⟩ = 1 := by
    have : a ⟨e, hEM he⟩ ∈ (E.subgroupOf M).map a :=
      ⟨⟨e, hEM he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
    rw [hbot] at this
    exact this
  obtain ⟨n, hn⟩ := hE2 ⟨e, he⟩
  exact mem_pCoreOf_of_ker h hd h1 ⟨n, by simpa using congrArg Subtype.val hn⟩

omit [Fintype F] in
theorem map_T_le_of_qv_le_vPre (h : PUHyp M T L) {Y : Subgroup ↥(StatedSp 2 F)}
    (hT : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a Y) : (T.subgroupOf M).map a ≤ Y := by
  rintro _ ⟨m, hm, rfl⟩
  have hmT : (puAmalgam h.le).ofA m ∈ Qv _ (baseB (puAmalgam h.le)) := by
    rw [puAmalgam.qv_baseB]
    exact ⟨m, hm, rfl⟩
  obtain ⟨m', hm', he⟩ := hT hmT
  rw [(puAmalgam h.le).ofA_injective he] at hm'
  exact hm'

omit [Fintype F] in
theorem vIm_qv_baseB (h : PUHyp M T L) :
    S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le))) = (T.subgroupOf M).map a := by
  rw [S5.vIm, puAmalgam.qv_baseB]
  ext x
  constructor
  · rintro ⟨m, ⟨m', hm', he⟩, rfl⟩
    rw [(puAmalgam h.le).ofA_injective he] at hm'
    exact ⟨m, hm', rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, ⟨m, hm, rfl⟩, rfl⟩

omit [Fintype F] in
theorem le_imM_of_le_vPre (h : PUHyp M T L) {Y : Subgroup ↥(StatedSp 2 F)}
    {J : Subgroup (puAmalgam h.le).Universal} (hJ : J ≤ S5.vPre h.le a Y) :
    J ≤ imM h.le ((Y.comap a).map M.subtype) ∧
      (((Y.comap a).map M.subtype).subgroupOf M).map a ≤ Y := by
  refine ⟨hJ.trans ?_, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.2 ⟨m, hm, rfl⟩, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨m', hm', he⟩ := Subgroup.mem_subgroupOf.1 hm
    rw [Subtype.ext he] at hm'
    exact hm'

theorem commutator_le_centralizer_jOff_one_baseA (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) (h54 : S54)
    {A : Subgroup (puAmalgam h.le).Universal} (hA : A ≤ Qv _ (baseB (puAmalgam h.le)))
    (hcard : Nat.card ↥⁅S5.uSub h.le L (baseA (puAmalgam h.le)), A⁆ ≤ 2 ^ k) :
    ⁅S5.uSub h.le L (baseA (puAmalgam h.le)), A⁆ ≤
      Subgroup.centralizer (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) : Set _) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  rw [puAmalgam.qv_baseB] at hA
  obtain ⟨A₀, hA₀T, hA₀M, rfl⟩ := S5B.exists_eq_imM h.le hA
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  rw [uSub_baseA h, ← imM_commutator h.le hUM hA₀M] at hcard ⊢
  rw [card_imM h.le (commutator_le_of_le hUM hA₀M)] at hcard
  by_cases hAO : A₀ ≤ pCoreOf 2 M
  · have hbot : ⁅Uq M T L, A₀⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      refine (h.Uq_le_Xq.trans ?_).trans (Subgroup.centralizer_le hAO)
      exact (PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right
    rw [hbot, imM, Subgroup.bot_subgroupOf, Subgroup.map_bot]
    exact bot_le
  have hA2 : IsPGroup 2 A₀ := h.isPGroup.to_le hA₀T
  obtain ⟨p, hp, hcomm, -, hxp, -⟩ :=
    exists_point_of_card_commutator_le h hd hlift hA₀M hA2 hAO hcard
  obtain ⟨g, hgA, hg1⟩ := exists_ne_one_of_ne_bot (map_ne_bot_of_not_le h hd hA₀M hA2 hAO)
  have hAT : ∀ x ∈ (A₀.subgroupOf M).map a, x ∈ (T.subgroupOf M).map a := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.2 (hA₀T (Subgroup.mem_subgroupOf.1 hm)), rfl⟩
  have hvec : ∀ y (hy : y ∈ Uq M T L), ∀ m (hm : m ∈ A₀),
      MSP.mat (a ⟨m, hA₀M hm⟩) *ᵥ c.vec ⟨y, hy⟩ - c.vec ⟨y, hy⟩ ∈ p := fun y hy m hm => by
    have hmA : a ⟨m, hA₀M hm⟩ ∈ (A₀.subgroupOf M).map a :=
      ⟨⟨m, hA₀M hm⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
    rw [← hcomm]
    exact MSP.sub_mem_commSp hmA _
  suffices hJ : ∃ J₀ : Subgroup G, J₀ ≤ M ∧
      S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤ imM h.le J₀ ∧
      (J₀.subgroupOf M).map a ≤ MSP.fixer p by
    obtain ⟨J₀, hJ₀M, hJJ, hJp⟩ := hJ
    exact imM_le_centralizer h.le hJ₀M
      (commutator_le_centralizer_of_vec h hlift c le_rfl hA₀M hvec hJ₀M hJp) hJJ
  rcases h54 G M T L h hmin hb k F _ _ a hd with
    ⟨-, ⟨l, hl, hTl, hJl⟩, -⟩ | ⟨-, hJT, p₀, hp₀, hTq⟩
  · have hpl := le_of_mem_xPoint_stab hp hl (hxp hgA)
      (map_T_le_of_qv_le_vPre h hTl (hAT g hgA)) hg1
    obtain ⟨hJ1, hJ2⟩ := le_imM_of_le_vPre h hJl
    exact ⟨_, Subgroup.map_subtype_le _, hJ1, hJ2.trans (MSP.fixer_antitone hpl)⟩
  · have hTq' : (T.subgroupOf M).map a = MSP.qPoint p₀ := by
      rw [← hTq, vIm_qv_baseB h]
    have hpp : p = p₀ := eq_of_mem_xPoint_qPoint hp hp₀ (hxp hgA) (hTq' ▸ hAT g hgA) hg1
    refine ⟨T, h.le, ?_, ?_⟩
    · rw [hJT, puAmalgam.qv_baseB]
    · rw [hTq', ← hpp]
      exact MSP.qPoint_le_fixer p

theorem commutator_le_centralizer_jOff_two_baseA (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) (h54 : S54)
    {A Z : Subgroup (puAmalgam h.le).Universal} (hA : A ≤ Qv _ (baseB (puAmalgam h.le)))
    (hZ : Z ≤ Qv _ (baseB (puAmalgam h.le))) (hZQ : ¬ Z ≤ Qv _ (baseA (puAmalgam h.le)))
    (hquad : ⁅⁅S5.uSub h.le L (baseA (puAmalgam h.le)), Z⁆, Z⁆ = ⊥)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set (puAmalgam h.le).Universal)) :
    ⁅S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (Z : Set (puAmalgam h.le).Universal), A⁆ ≤
      Subgroup.centralizer (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) : Set _) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hd.2.1
  rw [puAmalgam.qv_baseB] at hA hZ
  obtain ⟨A₀, hA₀T, hA₀M, rfl⟩ := S5B.exists_eq_imM h.le hA
  obtain ⟨Z₀, hZ₀T, hZ₀M, rfl⟩ := S5B.exists_eq_imM h.le hZ
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hZ₀O : ¬ Z₀ ≤ pCoreOf 2 M := fun hle =>
    hZQ (by rw [qv_baseA_eq h]; exact imM_mono h.le hle)
  have hZ₀2 : IsPGroup 2 Z₀ := h.isPGroup.to_le hZ₀T
  have hquad₀ : ⁅⁅Uq M T L, Z₀⁆, Z₀⁆ = ⊥ := by
    have hc1 : ⁅Uq M T L, Z₀⁆ ≤ M := commutator_le_of_le hUM hZ₀M
    rw [uSub_baseA h, ← imM_commutator h.le hUM hZ₀M, ← imM_commutator h.le hc1 hZ₀M] at hquad
    exact (imM_eq_bot_iff h.le (commutator_le_of_le hc1 hZ₀M)).1 hquad
  set Zb := (Z₀.subgroupOf M).map a with hZb
  have hZb1 : Zb ≠ ⊥ := map_ne_bot_of_not_le h hd hZ₀M hZ₀2 hZ₀O
  have hquadSp : MSP.commSp Zb ≤ MSP.fixSp Zb := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := exists_mem_commutator_vec_eq h c hw
    refine (mem_centralizer_iff_vec h hlift c hZ₀M x).1 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : ⁅(x : G), z⁆ ∈ ⁅⁅Uq M T L, Z₀⁆, Z₀⁆ := Subgroup.commutator_mem_commutator hx hz
    rw [hquad₀, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hAZ₀ : ∀ m ∈ A₀, ∀ z ∈ Z₀, m * z * m⁻¹ ∈ Z₀ := by
    intro m hm z hz
    have h1 : (puAmalgam h.le).ofA ⟨m, hA₀M hm⟩ ∈ imM h.le A₀ :=
      ⟨⟨m, hA₀M hm⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
    have h2 : (puAmalgam h.le).ofA ⟨z, hZ₀M hz⟩ ∈ imM h.le Z₀ :=
      ⟨⟨z, hZ₀M hz⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
    have h3 := (Subgroup.mem_normalizer_iff.1 (hAZ h1) _).1 h2
    obtain ⟨w, hw, he⟩ := h3
    have h4 : w = ⟨m, hA₀M hm⟩ * ⟨z, hZ₀M hz⟩ * ⟨m, hA₀M hm⟩⁻¹ :=
      (puAmalgam h.le).ofA_injective (by rw [he, map_mul, map_mul, map_inv])
    rw [h4] at hw
    exact Subgroup.mem_subgroupOf.1 hw
  have hAZb : ∀ m (hm : m ∈ A₀), a ⟨m, hA₀M hm⟩ ∈ Subgroup.normalizer (Zb : Set _) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨m, hA₀M hm⟩ * z * ⟨m, hA₀M hm⟩⁻¹, ?_, by simp [map_mul, map_inv]⟩
      exact Subgroup.mem_subgroupOf.2 (hAZ₀ m hm z (Subgroup.mem_subgroupOf.1 hz))
    · rintro ⟨z, hz, hzx⟩
      refine ⟨⟨m, hA₀M hm⟩⁻¹ * z * ⟨m, hA₀M hm⟩, ?_, ?_⟩
      · have := hAZ₀ m⁻¹ (inv_mem hm) z (Subgroup.mem_subgroupOf.1 hz)
        rw [inv_inv] at this
        exact Subgroup.mem_subgroupOf.2 this
      · rw [map_mul, map_mul, hzx, map_inv]
        group
  have hA2 : ∀ m (hm : m ∈ A₀), ∃ n : ℕ, a ⟨m, hA₀M hm⟩ ^ 2 ^ n = 1 := by
    intro m hm
    obtain ⟨n, hn⟩ := h.isPGroup ⟨m, hA₀T hm⟩
    refine ⟨n, ?_⟩
    have h1 : (⟨m, hA₀M hm⟩ : ↥M) ^ 2 ^ n = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hn)
    rw [← map_pow, h1, map_one]
  have hAT : ∀ m (hm : m ∈ A₀), a ⟨m, hA₀M hm⟩ ∈ (T.subgroupOf M).map a :=
    fun m hm => ⟨⟨m, hA₀M hm⟩, Subgroup.mem_subgroupOf.2 (hA₀T hm), rfl⟩
  have hZT : Zb ≤ (T.subgroupOf M).map a := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.2 (hZ₀T (Subgroup.mem_subgroupOf.1 hx))
  rw [uSub_baseA h, ← imM_inf_centralizer h.le _ hZ₀M,
    ← imM_commutator h.le (inf_le_left.trans hUM) hA₀M]
  suffices hJ : ∃ (W : Submodule F (MSP.V4 F)) (J₀ : Subgroup G), J₀ ≤ M ∧
      S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤ imM h.le J₀ ∧
      (J₀.subgroupOf M).map a ≤ MSP.fixer W ∧
      ∀ m (hm : m ∈ A₀), ∀ v ∈ MSP.fixSp Zb, MSP.mat (a ⟨m, hA₀M hm⟩) *ᵥ v - v ∈ W by
    obtain ⟨W, J₀, hJ₀M, hJJ, hJW, hW⟩ := hJ
    refine imM_le_centralizer h.le hJ₀M ?_ hJJ
    refine commutator_le_centralizer_of_vec h hlift c inf_le_left hA₀M
      (fun y hy m hm => hW m hm _ ?_) hJ₀M hJW
    exact (mem_centralizer_iff_vec h hlift c hZ₀M ⟨y, hy.1⟩).1 hy.2
  rcases h54 G M T L h hmin hb k F _ _ a hd with
    ⟨-, ⟨l, hl, hTl, hJl⟩, -⟩ | ⟨-, hJT, p₀, hp₀, hTq⟩
  · obtain ⟨hJ1, hJ2⟩ := le_imM_of_le_vPre h hJl
    have hTl' := map_T_le_of_qv_le_vPre h hTl
    refine ⟨l, _, Subgroup.map_subtype_le _, hJ1, hJ2, fun m hm v hv => ?_⟩
    obtain ⟨n, hn⟩ := hA2 m hm
    exact sub_mem_line_of_quad hl (hZT.trans hTl') hZb1 hquadSp hn (hTl' (hAT m hm))
      (hAZb m hm) hv
  · have hTq' : (T.subgroupOf M).map a = MSP.qPoint p₀ := by
      rw [← hTq, vIm_qv_baseB h]
    refine ⟨p₀, T, h.le, ?_, ?_, fun m hm v hv => ?_⟩
    · rw [hJT, puAmalgam.qv_baseB]
    · rw [hTq']
      exact MSP.qPoint_le_fixer p₀
    · have hv' := fixSp_le_perp_of_le_qPoint hp₀ (hTq' ▸ hZT) hZb1 hv
      have hq : a ⟨m, hA₀M hm⟩ ∈ MSP.qPoint p₀ := hTq' ▸ hAT m hm
      exact hq.2 v hv'

end Base

section Edge

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commutator_le_centralizer_jOff_one (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) (h54 : S54)
    {ρ ν : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) (hρν : (puAmalgam h.le).treeGraph.Adj ρ ν)
    {A : Subgroup (puAmalgam h.le).Universal} (hA : A ≤ Qv _ ν)
    (hcard : Nat.card ↥⁅S5.uSub h.le L ρ, A⁆ ≤ 2 ^ k) :
    ⁅S5.uSub h.le L ρ, A⁆ ≤ Subgroup.centralizer (S5.jOff h.le L (2 ^ k) ρ ν : Set _) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hρ hρν
  have hAA : A = (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv A g).symm
  rw [hAA] at hA hcard ⊢
  rw [qv_smul, map_conj_le_map_conj_iff] at hA
  rw [uSub_smul h.le hLn, ← Subgroup.map_commutator, card_map_conj] at hcard
  rw [jOff_smul h.le hLn, uSub_smul h.le hLn, ← Subgroup.map_commutator,
    PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff]
  exact commutator_le_centralizer_jOff_one_baseA h hmin hb hd h54 hA hcard

theorem commutator_le_centralizer_jOff_two (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) (h54 : S54)
    {ρ ν : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) (hρν : (puAmalgam h.le).treeGraph.Adj ρ ν)
    {A Z : Subgroup (puAmalgam h.le).Universal} (hA : A ≤ Qv _ ν) (hZ : Z ≤ Qv _ ν)
    (hZQ : ¬ Z ≤ Qv _ ρ) (hquad : ⁅⁅S5.uSub h.le L ρ, Z⁆, Z⁆ = ⊥)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set (puAmalgam h.le).Universal)) :
    ⁅S5.uSub h.le L ρ ⊓ Subgroup.centralizer (Z : Set (puAmalgam h.le).Universal), A⁆ ≤
      Subgroup.centralizer (S5.jOff h.le L (2 ^ k) ρ ν : Set _) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hρ hρν
  set A' := A.map (MulAut.conj g⁻¹).toMonoidHom with hA'
  set Z' := Z.map (MulAut.conj g⁻¹).toMonoidHom with hZ'
  have hAA : A = A'.map (MulAut.conj g).toMonoidHom := (map_conj_map_conj_inv A g).symm
  have hZZ : Z = Z'.map (MulAut.conj g).toMonoidHom := (map_conj_map_conj_inv Z g).symm
  clear_value A' Z'
  subst hAA hZZ
  rw [qv_smul, map_conj_le_map_conj_iff] at hA hZ hZQ
  rw [uSub_smul h.le hLn, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
    Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at hquad
  rw [normalizer_map_conj, map_conj_le_map_conj_iff] at hAZ
  have hC : Subgroup.centralizer ((Z'.map (MulAut.conj g).toMonoidHom : Subgroup _) :
      Set (puAmalgam h.le).Universal) =
      (Subgroup.centralizer (Z' : Set (puAmalgam h.le).Universal)).map
        (MulAut.conj g).toMonoidHom := PU.centralizer_map_mulEquiv _ _
  have hCJ : Subgroup.centralizer ((S5.jOff h.le L (2 ^ k) (g • baseA (puAmalgam h.le))
      (g • baseB _) : Subgroup _) : Set (puAmalgam h.le).Universal) =
      (Subgroup.centralizer (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) :
        Set (puAmalgam h.le).Universal)).map (MulAut.conj g).toMonoidHom := by
    rw [jOff_smul h.le hLn]
    exact PU.centralizer_map_mulEquiv _ _
  rw [hCJ, uSub_smul h.le hLn, hC, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← Subgroup.map_commutator, map_conj_le_map_conj_iff]
  exact commutator_le_centralizer_jOff_two_baseA h hmin hb hd h54 hA hZ hZQ hquad hAZ

end Edge

end S5B

end CFSG.Quasithin.MS93
