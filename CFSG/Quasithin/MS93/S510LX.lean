module

public import CFSG.Quasithin.MS93.S510Om
public import CFSG.Quasithin.MS93.S510Loc
public import CFSG.Quasithin.MS93.S59Om
public import CFSG.Quasithin.MS93.S510Tv

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S510

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem localX_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E₀ A₀ J₀ : Subgroup G} (hE₀T : E₀ ≤ T) (hA₀T : A₀ ≤ T) (hJ₀T : J₀ ≤ T)
    (hrel : (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) = 2 ^ k)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : (T.subgroupOf M).map a ≤ MSP.stab l) (hJl : (J₀.subgroupOf M).map a ≤ MSP.qLine l)
    (hJc : 2 ^ k < Nat.card ((J₀.subgroupOf M).map a))
    (hcen : (⁅Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G), A₀⁆ ⊔ ⁅Uq M T L, E₀⁆) ⊓
        Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer (M : Set G))
    (hR : ⁅Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G), A₀⁆ ≠ ⊥) :
    ⁅Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G), A₀⁆ ≤ Subgroup.centralizer (J₀ : Set G) ∧
      Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤
        ⁅Uq M T L, E₀⁆ ⊔ ⁅Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G), A₀⁆ := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hd.2.1
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hE₀M : E₀ ≤ M := hE₀T.trans h.le
  have hA₀M : A₀ ≤ M := hA₀T.trans h.le
  set R := ⁅Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G), A₀⁆ with hRdef
  set W := ⁅Uq M T L, E₀⁆ with hWdef
  set Tb := (T.subgroupOf M).map a with hTb
  set Eb := (E₀.subgroupOf M).map a with hEb
  set Jb := (J₀.subgroupOf M).map a with hJb
  set P₀ := MSP.fixSp Tb with hP₀
  have hkey : ∀ u : ↥(Uq M T L), (u : G) ∈ R ⊔ W → c.vec u ∈ P₀ → c.vec u = 0 := by
    intro u hu hP
    have huT : (u : G) ∈ Subgroup.centralizer (T : Set G) :=
      (S5B.mem_centralizer_iff_vec h hlift c h.le u).2 hP
    exact (c.vec_eq_zero_iff u).2 ⟨u.2, Subgroup.centralizer_le h.L_le (hcen ⟨hu, huT⟩)⟩
  obtain ⟨p, hp, hpc, hpf, hEX⟩ := exists_point_of_relIndex h hd hE₀M hrel
  have hEb1 : Eb ≠ ⊥ := by
    intro hbot
    have h1 : MSP.fixSp Eb = ⊤ := MSP.fixSp_eq_top_iff.2 hbot
    rw [hpf] at h1
    have h2 := MSP.finrank_perp p
    rw [h1, finrank_top] at h2
    have h3 : Module.finrank F p = 1 := hp
    have h4 : Module.finrank F (MSP.V4 F) = 4 := by simp
    omega
  obtain ⟨e, he, he1⟩ : ∃ e ∈ Eb, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hEb1 (eq_bot_iff.2 fun e he => Subgroup.mem_bot.2 (hcon e he))
  have hET : Eb ≤ Tb := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.2 (hE₀T (Subgroup.mem_subgroupOf.1 hx))
  have hJT : Jb ≤ Tb := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.2 (hJ₀T (Subgroup.mem_subgroupOf.1 hx))
  have hpl : p ≤ l := S5B.le_of_mem_xPoint_stab hp hl (hEX he) (hTl (hET he)) he1
  have hlp : l ≤ MSP.perp p := by
    have := MSP.perp_antitone hpl
    rwa [hl.perp_eq] at this
  have hJfix : MSP.fixSp Jb = l := S5B.fixSp_eq_of_le_qLine hl hJl (by rw [hFq]; exact hJc)
  have hP₀l : P₀ ≤ l := hJfix ▸ MSP.fixSp_antitone hJT
  have hTb2 : IsPGroup 2 Tb :=
    (h.isPGroup.comap_of_injective M.subtype (Subgroup.subtype_injective M)).map a
  have hP₀0 : P₀ ≠ ⊥ := S5.fixSp_ne_bot hTb2
  have hpP : p ⊓ P₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwp, hwP⟩
    rw [← hpc] at hwp
    obtain ⟨u, hu, rfl⟩ := S5B.exists_mem_commutator_vec_eq h c hwp
    exact (Submodule.mem_bot F).2 (hkey u (Subgroup.mem_sup_right hu) hwP)
  have hsup : p ⊔ P₀ = l := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq p P₀
    rw [hpP, finrank_bot] at h1
    have h2 := Submodule.finrank_mono (sup_le hpl hP₀l)
    rw [hl.1] at h2
    have h3 := S5.finrank_pos_of_ne_bot hP₀0
    have hp1 : Module.finrank F p = 1 := hp
    exact Submodule.eq_of_le_of_finrank_eq (sup_le hpl hP₀l) (by rw [hl.1]; omega)
  obtain ⟨v, hv0, hpv⟩ := MSP.exists_eq_span_of_isPoint hp
  have hvP : v ∉ P₀ := by
    intro hv
    have : v ∈ p ⊓ P₀ := ⟨hpv ▸ Submodule.mem_span_singleton_self v, hv⟩
    rw [hpP] at this
    exact hv0 ((Submodule.mem_bot F).1 this)
  have hlv : l = P₀ ⊔ F ∙ v := by rw [← hsup, hpv, sup_comm]
  have hcomm : ∀ a₀ (ha₀ : a₀ ∈ A₀), ∀ y ∈ MSP.perp p, ∃ r : ↥(Uq M T L), (r : G) ∈ R ∧
      c.vec r = MSP.mat (a ⟨a₀, hA₀M ha₀⟩) *ᵥ y - y := by
    intro a₀ ha₀ y hy
    obtain ⟨u, rfl⟩ := c.exists_vec_eq y
    have huE : (u : G) ∈ Subgroup.centralizer (E₀ : Set G) :=
      (S5B.mem_centralizer_iff_vec h hlift c hE₀M u).2 (hpf ▸ hy)
    have hconj : a₀ * u * a₀⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hUn (hA₀M ha₀)) u).1 u.2
    refine ⟨⟨_, mul_mem hconj (inv_mem u.2)⟩, ?_, c.vec_commutator ⟨a₀, hA₀M ha₀⟩ u hconj⟩
    have := Subgroup.commutator_mem_commutator ha₀ (Subgroup.mem_inf.2 ⟨u.2, huE⟩)
    rw [Subgroup.commutator_comm] at this
    rwa [commutatorElement_def] at this
  have hA : ∀ a₀ (ha₀ : a₀ ∈ A₀), ∀ y ∈ MSP.perp p,
      MSP.mat (a ⟨a₀, hA₀M ha₀⟩) *ᵥ y - y ∈ p := by
    intro a₀ ha₀
    set g := a ⟨a₀, hA₀M ha₀⟩ with hg
    have hgT : g ∈ Tb := ⟨⟨a₀, hA₀M ha₀⟩, Subgroup.mem_subgroupOf.2 (hA₀T ha₀), rfl⟩
    have hgP₀ : ∀ x ∈ P₀, MSP.mat g *ᵥ x = x := fun x hx => hx g hgT
    have hgl : g ∈ MSP.stab l := hTl hgT
    obtain ⟨n, hn⟩ := h.isPGroup ⟨a₀, hA₀T ha₀⟩
    have hgn : g ^ 2 ^ n = 1 := by
      have h1 : (⟨a₀, hA₀M ha₀⟩ : ↥M) ^ 2 ^ n = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hn)
      rw [hg, ← map_pow, h1, map_one]
    have hvl : v ∈ l := hpl (hpv ▸ Submodule.mem_span_singleton_self v)
    have hgv : MSP.mat g *ᵥ v - v ∈ P₀ :=
      S5.sub_mem_of_pow hgn hgP₀ hvP (hlv ▸ MSP.mulVec_mem_of_mem_stab hgl hvl)
    have hlP : ∀ y ∈ l, MSP.mat g *ᵥ y - y ∈ P₀ := by
      intro y hy
      rw [hlv] at hy
      obtain ⟨y₀, hy₀, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hz
      have e1 : MSP.mat g *ᵥ (y₀ + d • v) - (y₀ + d • v) = d • (MSP.mat g *ᵥ v - v) := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, hgP₀ y₀ hy₀, smul_sub]
        abel
      rw [e1]
      exact P₀.smul_mem d hgv
    have hgfix : g ∈ MSP.fixer l := by
      intro y hy
      obtain ⟨r, hr, hrv⟩ := hcomm a₀ ha₀ y (hlp hy)
      have h0 := hkey r (Subgroup.mem_sup_left hr) (hrv ▸ hlP y hy)
      rw [hrv] at h0
      exact sub_eq_zero.1 h0
    intro y hy
    have hmem : MSP.mat g *ᵥ y - y ∈ l := hl.perp_eq ▸ MSP.sub_mem_perp_of_mem_fixer hgfix y
    rw [← hsup] at hmem
    obtain ⟨w₁, hw₁, w₂, hw₂, hw⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨x, hx, hxv⟩ := S5B.exists_mem_commutator_vec_eq h c (show w₁ ∈ MSP.commSp Eb from
      hpc ▸ hw₁)
    obtain ⟨r, hr, hrv⟩ := hcomm a₀ ha₀ y hy
    have e2 : c.vec (r * x⁻¹) = w₂ := by
      rw [c.vec_mul, c.vec_inv, hrv, hxv, ← hw]
      abel
    have hz := hkey (r * x⁻¹)
      (mul_mem (Subgroup.mem_sup_left hr) (inv_mem (Subgroup.mem_sup_right hx))) (e2 ▸ hw₂)
    rw [e2] at hz
    rw [← hw, hz, add_zero]
    exact hw₁
  refine ⟨?_, ?_⟩
  ·
    rw [Subgroup.commutator_le]
    intro u hu a₀ ha₀
    have hconj : a₀ * u * a₀⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hUn (hA₀M ha₀)) u).1 hu.1
    have hcU : a₀ * u * a₀⁻¹ * u⁻¹ ∈ Uq M T L := mul_mem hconj (inv_mem hu.1)
    have hrU : ⁅u, a₀⁆ ∈ Uq M T L := by
      have e : ⁅u, a₀⁆ = (a₀ * u * a₀⁻¹ * u⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      rw [e]
      exact inv_mem hcU
    have huv : c.vec ⟨u, hu.1⟩ ∈ MSP.perp p :=
      hpf ▸ (S5B.mem_centralizer_iff_vec h hlift c hE₀M ⟨u, hu.1⟩).1 hu.2
    have hrv : c.vec ⟨⁅u, a₀⁆, hrU⟩ ∈ p := by
      have e : (⟨⁅u, a₀⁆, hrU⟩ : ↥(Uq M T L)) = (⟨_, hcU⟩ : ↥(Uq M T L))⁻¹ :=
        Subtype.ext (by
          show ⁅u, a₀⁆ = (a₀ * u * a₀⁻¹ * u⁻¹)⁻¹
          rw [commutatorElement_def]
          group)
      rw [e, c.vec_inv, c.vec_commutator ⟨a₀, hA₀M ha₀⟩ ⟨u, hu.1⟩ hconj]
      exact p.neg_mem (hA a₀ ha₀ _ huv)
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjM : j ∈ M := hJ₀T.trans h.le hj
    have hjl : a ⟨j, hjM⟩ ∈ MSP.qLine l := hJl ⟨⟨j, hjM⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
    have hconj' : j * ⁅u, a₀⁆ * j⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hUn hjM) _).1 hrU
    have h0 : c.vec ⟨j * ⁅u, a₀⁆ * j⁻¹ * ⁅u, a₀⁆⁻¹, mul_mem hconj' (inv_mem hrU)⟩ = 0 := by
      rw [c.vec_commutator ⟨j, hjM⟩ ⟨_, hrU⟩ hconj', hjl _ (hpl hrv), sub_self]
    have h1 := hlift j hjM _ hrU ((c.vec_eq_zero_iff _).1 h0).2
    calc j * ⁅u, a₀⁆ = j * ⁅u, a₀⁆ * j⁻¹ * j := by group
      _ = ⁅u, a₀⁆ * j := by rw [h1]
  ·
    have hnc : ¬ Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G) ≤
        Subgroup.centralizer (A₀ : Set G) := fun hle =>
      hR (Subgroup.commutator_eq_bot_iff_le_centralizer.2 hle)
    obtain ⟨u, hu, hnu⟩ := Set.not_subset.1 hnc
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hnu
    push Not at hnu
    obtain ⟨a₀, ha₀, hne⟩ := hnu
    have hconj : a₀ * u * a₀⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hUn (hA₀M ha₀)) u).1 hu.1
    have huv : c.vec ⟨u, hu.1⟩ ∈ MSP.perp p :=
      hpf ▸ (S5B.mem_centralizer_iff_vec h hlift c hE₀M ⟨u, hu.1⟩).1 hu.2
    have hx₀ : MSP.mat (a ⟨a₀, hA₀M ha₀⟩) *ᵥ c.vec ⟨u, hu.1⟩ ≠ c.vec ⟨u, hu.1⟩ := by
      intro heq
      apply hne
      have h0 : c.vec ⟨a₀ * u * a₀⁻¹ * u⁻¹, mul_mem hconj (inv_mem hu.1)⟩ = 0 := by
        rw [c.vec_commutator ⟨a₀, hA₀M ha₀⟩ ⟨u, hu.1⟩ hconj, heq, sub_self]
      have h1 := hlift a₀ (hA₀M ha₀) u hu.1 ((c.vec_eq_zero_iff _).1 h0).2
      calc a₀ * u = a₀ * u * a₀⁻¹ * a₀ := by group
        _ = u * a₀ := by rw [h1]
    obtain ⟨ψ, hψU, hψs, hψe, hψZ⟩ := S59.exists_omega5_cover h hd
    refine uq_inf_le_of_transv hd hψU hψs hψe hψZ hE₀M hv0 (hpv ▸ hEX) hEb1
      (a₀ := ⟨a₀, hA₀M ha₀⟩) ha₀ (fun x hx => hpv ▸ hA a₀ ha₀ x (hpv ▸ hx))
      ⟨_, hpv ▸ huv, hx₀⟩

theorem localX_baseA (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hlc : LineCase h (2 ^ k) a)
    (hJq : (2 ^ k) ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex
      (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)))
    {E A₀ : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ Qv _ (baseB (puAmalgam h.le))) (hA : A₀ ≤ Qv _ (baseB (puAmalgam h.le)))
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (baseA _)) = 2 ^ k)
    (hcen : (⁅S5.uSub h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set _), A₀⁆ ⊔
        ⁅S5.uSub h.le L (baseA _), E⁆) ⊓
          Subgroup.centralizer (Qv _ (baseB (puAmalgam h.le)) : Set _) ≤
        stabCenter _ (baseA (puAmalgam h.le)))
    (hR : ⁅S5.uSub h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set _), A₀⁆ ≠ ⊥) :
    ⁅S5.uSub h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set _), A₀⁆ ≤
        Subgroup.centralizer (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) : Set _) ∧
      S5.uSub h.le L (baseA _) ⊓
          Subgroup.centralizer (puTrans h.le L (baseA (puAmalgam h.le)) : Set _) ≤
        ⁅S5.uSub h.le L (baseA _), E⁆ ⊔
          ⁅S5.uSub h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set _), A₀⁆ := by
  obtain ⟨l, hl, hTl, hJl⟩ := hlc
  have hJT := S5B.jOff_le_qv h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)
  have hJc0 := S5B.relIndex_le_card_vIm h hd hJT
  rw [puAmalgam.qv_baseB] at hE hA hcen hJT hTl
  obtain ⟨E₀, hE₀T, hE₀M, rfl⟩ := S5B.exists_eq_imM h.le hE
  obtain ⟨A₁, hA₁T, hA₁M, rfl⟩ := S5B.exists_eq_imM h.le hA
  obtain ⟨J₀, hJ₀T, hJ₀M, hJeq⟩ := S5B.exists_eq_imM h.le hJT
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hCM : Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G) ≤ M := inf_le_left.trans hUM
  have hR₀M : ⁅Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G), A₁⁆ ≤ M :=
    commutator_le_of_le hCM hA₁M
  have hW₀M : ⁅Uq M T L, E₀⁆ ≤ M := commutator_le_of_le hUM hE₀M
  have hrw1 : S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (imM h.le E₀ : Set (puAmalgam h.le).Universal) =
      imM h.le (Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G)) := by
    rw [S5B.uSub_baseA h, imM_inf_centralizer h.le _ hE₀M]
  have hrw2 : ⁅S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (imM h.le E₀ : Set (puAmalgam h.le).Universal), imM h.le A₁⁆ =
      imM h.le ⁅Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G), A₁⁆ := by
    rw [hrw1, imM_commutator h.le hCM hA₁M]
  have hrw3 : ⁅S5.uSub h.le L (baseA (puAmalgam h.le)), imM h.le E₀⁆ =
      imM h.le ⁅Uq M T L, E₀⁆ := by
    rw [S5B.uSub_baseA h, imM_commutator h.le hUM hE₀M]
  rw [hrw2, hrw3] at hcen ⊢
  rw [hrw2] at hR
  rw [S5B.uSub_baseA h, S5B.relIndex_centralizer_imM h.le hUM hE₀M] at hrel
  rw [← S5B.imM_sup_of_le h.le hR₀M hW₀M, ← imM_inf_centralizer h.le _ h.le,
    S5B.stabCenter_baseA, imM_le_imM_iff h.le (inf_le_left.trans (sup_le hR₀M hW₀M))] at hcen
  rw [Ne, imM_eq_bot_iff h.le hR₀M] at hR
  have hTl' : (T.subgroupOf M).map a ≤ MSP.stab l := by
    have := S5B.vIm_le_of_le_vPre h.le hTl
    rwa [S5B.vIm_imM] at this
  rw [hJeq] at hJl hJc0 ⊢
  have hJl' : (J₀.subgroupOf M).map a ≤ MSP.qLine l := by
    have := S5B.vIm_le_of_le_vPre h.le hJl
    rwa [S5B.vIm_imM] at this
  rw [S5B.vIm_imM] at hJc0
  have hJc : 2 ^ k < Nat.card ((J₀.subgroupOf M).map a) := by
    have hk : 1 ≤ k := hd.1
    have h2 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rw [← hJeq] at hJc0
    have : 2 ^ k < (2 ^ k) ^ 2 := by nlinarith
    exact lt_of_lt_of_le this (hJq.trans (hJeq ▸ hJc0))
  obtain ⟨h1, h2⟩ := localX_M h hd hE₀T hA₁T hJ₀T hrel hl hTl' hJl' hJc
    (fun x hx => (hcen hx).2) hR
  refine ⟨?_, ?_⟩
  · have e : imM h.le ⁅Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G), A₁⁆ =
        imM h.le (⁅Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G), A₁⁆ ⊓
          Subgroup.centralizer (J₀ : Set G)) := by rw [inf_eq_left.2 h1]
    rw [e, imM_inf_centralizer h.le _ hJ₀M]
    exact inf_le_right
  · rw [S5B.uSub_baseA h, S5B.puTrans_L_baseA h, ← imM_inf_centralizer h.le _ h.L_le,
      ← S5B.imM_sup_of_le h.le hW₀M hR₀M]
    exact imM_mono h.le h2

theorem localX_gp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hlc : LineCase h (2 ^ k) a)
    (hJq : (2 ^ k) ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex
      (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)))
    {ρ ε : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) (hρε : (puAmalgam h.le).treeGraph.Adj ρ ε)
    {E A₀ : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ ε) (hA : A₀ ≤ Qv _ ε)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L ρ) = 2 ^ k)
    (hcen : (⁅S5.uSub h.le L ρ ⊓ Subgroup.centralizer (E : Set _), A₀⁆ ⊔
        ⁅S5.uSub h.le L ρ, E⁆) ⊓ Subgroup.centralizer (Qv _ ε : Set _) ≤ stabCenter _ ρ)
    (hR : ⁅S5.uSub h.le L ρ ⊓ Subgroup.centralizer (E : Set _), A₀⁆ ≠ ⊥) :
    ⁅S5.uSub h.le L ρ ⊓ Subgroup.centralizer (E : Set _), A₀⁆ ≤
        Subgroup.centralizer (S5.jOff h.le L (2 ^ k) ρ ε : Set _) ∧
      S5.uSub h.le L ρ ⊓ Subgroup.centralizer (puTrans h.le L ρ : Set _) ≤
        ⁅S5.uSub h.le L ρ, E⁆ ⊔ ⁅S5.uSub h.le L ρ ⊓ Subgroup.centralizer (E : Set _), A₀⁆ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hρ hρε
  have hEE : E = (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv E g).symm
  have hAA : A₀ = (A₀.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv A₀ g).symm
  set E' := E.map (MulAut.conj g⁻¹).toMonoidHom
  set A' := A₀.map (MulAut.conj g⁻¹).toMonoidHom
  rw [hEE, hAA] at hcen hR ⊢
  rw [hEE] at hE hrel
  rw [hAA] at hA
  rw [qv_smul, map_conj_le_map_conj_iff] at hE hA
  rw [S5B.uSub_smul h.le hLn, PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hrel
  have hrw : ⁅S5.uSub h.le L (g • baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (E'.map (MulAut.conj g).toMonoidHom : Set _),
        A'.map (MulAut.conj g).toMonoidHom⁆ =
      (⁅S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (E' : Set _), A'⁆).map
        (MulAut.conj g).toMonoidHom := by
    rw [S5B.uSub_smul h.le hLn, PU.centralizer_map_mulEquiv,
      ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, Subgroup.map_commutator]
  have hrw' : ⁅S5.uSub h.le L (g • baseA (puAmalgam h.le)), E'.map (MulAut.conj g).toMonoidHom⁆ =
      (⁅S5.uSub h.le L (baseA (puAmalgam h.le)), E'⁆).map (MulAut.conj g).toMonoidHom := by
    rw [S5B.uSub_smul h.le hLn, Subgroup.map_commutator]
  rw [hrw, hrw'] at hcen ⊢
  rw [hrw, Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at hR
  rw [← Subgroup.map_sup, qv_smul,
    PU.centralizer_map_mulEquiv (MulAut.conj g) (Qv _ (baseB (puAmalgam h.le))),
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, stabCenter_smul,
    map_conj_le_map_conj_iff] at hcen
  obtain ⟨h1, h2⟩ := localX_baseA h hd hlc hJq hE hA hrel hcen hR
  refine ⟨?_, ?_⟩
  · rw [S5B.jOff_smul h.le hLn,
      PU.centralizer_map_mulEquiv (MulAut.conj g) (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)),
      map_conj_le_map_conj_iff]
    exact h1
  · rw [S5B.uSub_smul h.le hLn, puTrans_smul h.le hLn,
      PU.centralizer_map_mulEquiv (MulAut.conj g) (puTrans h.le L (baseA (puAmalgam h.le))),
      ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← Subgroup.map_sup,
      map_conj_le_map_conj_iff]
    exact h2

theorem map_ne_qPoint_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E₀ : Subgroup G} (hE₀T : E₀ ≤ T)
    (hrel : (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) = 2 ^ k)
    (hRT : ⁅Uq M T L, E₀⁆ ⊓ Subgroup.centralizer (T : Set G) ≤
      Subgroup.centralizer (L : Set G))
    {p₀ : Submodule F (MSP.V4 F)} (hp₀ : MSP.IsPoint p₀) :
    (T.subgroupOf M).map a ≠ MSP.qPoint p₀ := by
  intro hT
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hE₀M : E₀ ≤ M := hE₀T.trans h.le
  obtain ⟨p, hp, hpc, hpf, hEX⟩ := exists_point_of_relIndex h hd hE₀M hrel
  have hEb1 : (E₀.subgroupOf M).map a ≠ ⊥ := by
    intro hbot
    have h1 : MSP.fixSp ((E₀.subgroupOf M).map a) = ⊤ := MSP.fixSp_eq_top_iff.2 hbot
    rw [hpf] at h1
    have h2 := MSP.finrank_perp p
    rw [h1, finrank_top] at h2
    have h3 : Module.finrank F p = 1 := hp
    have h4 : Module.finrank F (MSP.V4 F) = 4 := by simp
    omega
  obtain ⟨e, he, he1⟩ : ∃ e ∈ (E₀.subgroupOf M).map a, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hEb1 (eq_bot_iff.2 fun e he => Subgroup.mem_bot.2 (hcon e he))
  have heT : e ∈ (T.subgroupOf M).map a := by
    obtain ⟨m, hm, rfl⟩ := he
    exact ⟨m, Subgroup.mem_subgroupOf.2 (hE₀T (Subgroup.mem_subgroupOf.1 hm)), rfl⟩
  have hpp : p = p₀ := S5B.eq_of_mem_xPoint_qPoint hp hp₀ (hEX he) (hT ▸ heT) he1
  obtain ⟨v, hv0, hpv⟩ := MSP.exists_eq_span_of_isPoint hp
  have hvp : v ∈ p := hpv ▸ Submodule.mem_span_singleton_self v
  obtain ⟨u, hu, huv⟩ := S5B.exists_mem_commutator_vec_eq h c (show v ∈ MSP.commSp _ from
    hpc ▸ hvp)
  have hvT : c.vec u ∈ MSP.fixSp ((T.subgroupOf M).map a) := by
    rw [huv, hT]
    intro g hg
    exact hg.1 v (hpp ▸ hvp)
  have huT := (S5B.mem_centralizer_iff_vec h hlift c h.le u).2 hvT
  have h0 := (c.vec_eq_zero_iff u).2 ⟨u.2, hRT ⟨hu, huT⟩⟩
  exact hv0 (huv ▸ h0)

theorem vIm_ne_qPoint_gp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {ρ ε : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) (hρε : (puAmalgam h.le).treeGraph.Adj ρ ε)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ ε)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L ρ) = 2 ^ k)
    (hRT : ⁅S5.uSub h.le L ρ, E⁆ ⊓
        Subgroup.centralizer (Qv _ ε : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (puTrans h.le L ρ : Set (puAmalgam h.le).Universal))
    {p₀ : Submodule F (MSP.V4 F)} (hp₀ : MSP.IsPoint p₀) :
    S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le))) ≠ MSP.qPoint p₀ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hρ hρε
  have hEE : E = (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
    (map_conj_map_conj_inv E g).symm
  rw [hEE] at hE hRT hrel
  rw [qv_smul, map_conj_le_map_conj_iff, puAmalgam.qv_baseB] at hE
  obtain ⟨E₀, hE₀T, hE₀M, hE₀⟩ := S5B.exists_eq_imM h.le hE
  rw [hE₀] at hRT hrel
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S5B.relIndex_centralizer_imM h.le hUM hE₀M] at hrel
  rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, ← Subgroup.map_commutator, qv_smul,
    puAmalgam.qv_baseB, puTrans_smul h.le hLn, S5B.puTrans_L_baseA h,
    PU.centralizer_map_mulEquiv, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_le_map_conj_iff,
    ← imM_commutator h.le hUM hE₀M] at hRT
  have hcomm : ⁅Uq M T L, E₀⁆ ≤ M := commutator_le_of_le hUM hE₀M
  rw [puAmalgam.qv_baseB, S5B.vIm_imM]
  refine map_ne_qPoint_M h hd hE₀T hrel ?_ hp₀
  intro x hx
  have hxM : x ∈ M := hcomm hx.1
  have h1 : (puAmalgam h.le).ofA ⟨x, hxM⟩ ∈ imM h.le (⁅Uq M T L, E₀⁆ ⊓
      Subgroup.centralizer (T : Set G)) := ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  rw [imM_inf_centralizer h.le _ h.le] at h1
  have h2 := hRT h1
  have h3 : (puAmalgam h.le).ofA ⟨x, hxM⟩ ∈ imM h.le (⁅Uq M T L, E₀⁆ ⊓
      Subgroup.centralizer (L : Set G)) := by
    rw [imM_inf_centralizer h.le _ h.L_le]
    exact ⟨h1.1, h2⟩
  obtain ⟨m, hm, he⟩ := h3
  have : m = ⟨x, hxM⟩ := (puAmalgam h.le).ofA_injective he
  subst this
  exact (Subgroup.mem_subgroupOf.1 hm).2

theorem line54_of (h54 : S54) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {ρ ε : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) (hρε : (puAmalgam h.le).treeGraph.Adj ρ ε)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ ε)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L ρ) = 2 ^ k)
    (hRT : ⁅S5.uSub h.le L ρ, E⁆ ⊓
        Subgroup.centralizer (Qv _ ε : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (puTrans h.le L ρ : Set (puAmalgam h.le).Universal)) :
    LineCase h (2 ^ k) a ∧ (2 ^ k) ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex
      (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) := by
  rcases h54 G M T L h hmin hb k F _ _ a hd with ⟨-, hlc, hq⟩ | ⟨-, -, p₀, hp₀, hTq⟩
  · exact ⟨hlc, hq⟩
  · exact absurd hTq (vIm_ne_qPoint_gp h hd hρ hρε hE hrel hRT hp₀)

end S510

end CFSG.Quasithin.MS93
