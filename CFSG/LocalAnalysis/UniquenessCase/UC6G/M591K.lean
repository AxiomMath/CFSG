module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.M591R
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.UniquenessCase.UC6M591K

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC6.Mz614 (center_eq_bot_of_simple_uc6)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

noncomputable def KerKbar : Subgroup ↥m.M where
  carrier := {x | ∀ k ∈ m.K, (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ m.U}
  one_mem' := fun k _ => by simp
  mul_mem' := by
    intro a b ha hb k hk
    have h2 := m.conj_U_le a.2 _ (hb k hk)
    have e : ((a * b : m.M) : G) * k * ((a * b : m.M) : G)⁻¹ * k⁻¹ =
        ((a : G) * ((b : G) * k * (b : G)⁻¹ * k⁻¹) * (a : G)⁻¹) * ((a : G) * k * (a : G)⁻¹ * k⁻¹) := by
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
    rw [e]
    exact m.U.mul_mem h2 (ha k hk)
  inv_mem' := by
    intro a ha k hk
    have hk' : (a : G)⁻¹ * k * (a : G) ∈ m.K := by
      simpa using m.conj_mem_K (inv_mem a.2) hk
    have h1 := ha _ hk'
    have e : ((a⁻¹ : m.M) : G) * k * ((a⁻¹ : m.M) : G)⁻¹ * k⁻¹ =
        ((a : G) * ((a : G)⁻¹ * k * (a : G)) * (a : G)⁻¹ * ((a : G)⁻¹ * k * (a : G))⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv, inv_inv]
      group
    rw [e]
    exact m.U.inv_mem h1

instance KerKbar_normal (m : Mz614 Dat) : (m.KerKbar).Normal where
  conj_mem := by
    intro x hx g k hk
    have hk'' : (g : G)⁻¹ * k * (g : G) ∈ m.K := by
      simpa using m.conj_mem_K (inv_mem g.2) hk
    have h1 := m.conj_U_le g.2 _ (hx _ hk'')
    have e : ((g * x * g⁻¹ : m.M) : G) * k * ((g * x * g⁻¹ : m.M) : G)⁻¹ * k⁻¹ =
        (g : G) * ((x : G) * ((g : G)⁻¹ * k * (g : G)) * (x : G)⁻¹ *
          ((g : G)⁻¹ * k * (g : G))⁻¹) * (g : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h1

theorem mem_U_iff {c : G} (hc : c ∈ m.K) :
    c ∈ m.U ↔ (⟨c, hc⟩ : ↥m.K) ∈ CFSG.pPrimeCore m.r ↥m.K :=
  Subgroup.mem_map_iff_mem m.K.subtype_injective (x := ⟨c, hc⟩)

theorem mem_U_of_mem_KerKbar (h629 : m.C629) {c : G} (hcK : c ∈ m.K) (hcM : c ∈ m.M)
    (hc : (⟨c, hcM⟩ : ↥m.M) ∈ m.KerKbar) : c ∈ m.U := by
  haveI := h629.1
  have hcen := center_eq_bot_of_simple_uc6 h629.2
  rw [m.mem_U_iff hcK]
  have hmem : (QuotientGroup.mk ⟨c, hcK⟩ : m.Kbar) ∈ Subgroup.center m.Kbar := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 := (m.KerKbar.inv_mem hc) (k : G)⁻¹ (m.K.inv_mem k.2)
    have h2 : (c : G)⁻¹ * (k : G)⁻¹ * c * k ∈ m.U := by simpa using h1
    have h3 := (m.mem_U_iff (show (c : G)⁻¹ * (k : G)⁻¹ * c * k ∈ m.K from
      m.K.mul_mem (m.K.mul_mem (m.K.mul_mem (m.K.inv_mem hcK) (m.K.inv_mem k.2)) hcK) k.2)).1 h2
    convert h3 using 1
    apply Subtype.ext
    simp [mul_assoc]
  rw [hcen, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  exact hmem

noncomputable def fK : ↥m.K →* ↥m.M ⧸ m.KerKbar :=
  (QuotientGroup.mk' m.KerKbar).comp (Subgroup.inclusion m.K_le_M)

noncomputable def NK : Subgroup (↥m.M ⧸ m.KerKbar) := m.fK.range

theorem ker_fK (h629 : m.C629) : m.fK.ker = CFSG.pPrimeCore m.r ↥m.K := by
  ext k
  rw [MonoidHom.mem_ker, fK, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hk
    exact (m.mem_U_iff k.2).1 (m.mem_U_of_mem_KerKbar h629 k.2 (m.K_le_M k.2) hk)
  · intro hk k' hk'
    have hkU : (k : G) ∈ m.U := (m.mem_U_iff k.2).2 hk
    have h1 := (mem_normalizer_iff.1 (m.K_le_normalizer_U hk') (k : G)⁻¹).1 (m.U.inv_mem hkU)
    have e : ((Subgroup.inclusion m.K_le_M k : ↥m.M) : G) * k' *
        ((Subgroup.inclusion m.K_le_M k : ↥m.M) : G)⁻¹ * k'⁻¹ = (k : G) * (k' * (k : G)⁻¹ * k'⁻¹) := by
      simp only [Subgroup.coe_inclusion]
      group
    rw [e]
    exact m.U.mul_mem hkU h1

theorem NK_normal : (m.NK).Normal := by
  refine ⟨fun n hn y => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨⟨(g : G) * k * (g : G)⁻¹, m.conj_mem_K g.2 k.2⟩, ?_⟩
  simp only [fK, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1

noncomputable def equivNK (h629 : m.C629) : m.Kbar ≃* ↥m.NK :=
  haveI := CFSG.pPrimeCore_normal (p := m.r) (G := ↥m.K)
  (QuotientGroup.quotientMulEquivOfEq (m.ker_fK h629).symm).trans
    (QuotientGroup.quotientKerEquivRange m.fK)

theorem mem_U_of_mem_KerKbar' (h629 : m.C629) {c : ↥m.M} (hcK : (c : G) ∈ m.K) (hc : c ∈ m.KerKbar) :
    (c : G) ∈ m.U :=
  m.mem_U_of_mem_KerKbar h629 hcK c.2 hc

theorem NK_isSimple (h629 : m.C629) : IsSimpleGroup ↥m.NK :=
  (m.equivNK h629).isSimpleGroup_congr.mp h629.1

theorem NK_not_comm (h629 : m.C629) : ¬ IsMulCommutative ↥m.NK := by
  obtain ⟨a, b, hab⟩ := h629.2
  intro h
  apply hab
  apply (m.equivNK h629).injective
  rw [map_mul, map_mul]
  exact h.is_comm.comm _ _

theorem NK_centralizer (h629 : m.C629) :
    centralizer (m.NK : Set (↥m.M ⧸ m.KerKbar)) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  intro k hk
  have hk' : k⁻¹ ∈ m.K := m.K.inv_mem hk
  have hc := mem_centralizer_iff.1 hy (m.fK ⟨k⁻¹, hk'⟩) ⟨⟨k⁻¹, hk'⟩, rfl⟩
  simp only [fK, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hc
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
  have hcK : (g : G)⁻¹ * k * (g : G) * k⁻¹ ∈ m.K :=
    m.K.mul_mem (by simpa using m.conj_mem_K (inv_mem g.2) hk) hk'
  have hU := m.mem_U_of_mem_KerKbar' h629 (c := (Subgroup.inclusion m.K_le_M ⟨k⁻¹, hk'⟩ * g)⁻¹ *
    (g * Subgroup.inclusion m.K_le_M ⟨k⁻¹, hk'⟩)) (by simpa [mul_assoc] using hcK) hc
  have h2 := m.conj_U_le g.2 _ hU
  have h3 := m.U.inv_mem h2
  simpa [mul_assoc] using h3

theorem NK_pRank (h625 : m.C625) (h629 : m.C629) : CFSG.Open.pRank m.r m.NK = 1 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  haveI := CFSG.pPrimeCore_normal (p := m.r) (G := ↥m.K)
  have hNK : CFSG.Open.pRank m.r m.NK = CFSG.pRank m.r ↥m.NK := by
    have htop : (⊤ : Subgroup ↥m.NK).map m.NK.subtype = m.NK := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have := pRank_map_subtype_uc6 m.hr m.NK (⊤ : Subgroup ↥m.NK)
    rw [htop] at this
    rw [this, CFSG.SectionRank.pRank_eq_open_pRank_top]
  have hKbar : CFSG.pRank m.r m.Kbar = CFSG.Open.pRank m.r (⊤ : Subgroup ↥m.K) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_quotient_eq (CFSG.pPrimeCore m.r ↥m.K)
      ((Nat.Prime.coprime_iff_not_dvd m.hr).1 CFSG.pPrimeCore_coprime_card)
  have hK : CFSG.Open.pRank m.r (⊤ : Subgroup ↥m.K) = CFSG.Open.pRank m.r m.K := by
    have htop : (⊤ : Subgroup ↥m.K).map m.K.subtype = m.K := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have := pRank_map_subtype_uc6 m.hr m.K (⊤ : Subgroup ↥m.K)
    rw [htop] at this
    exact this.symm
  rw [hNK, CFSG.pRank_congr_of_mulEquiv (m.equivNK h629).symm m.r, hKbar, hK]
  exact h625

theorem EL_le_M : m.EL ≤ m.M := fun x hx => m.R_le_M (m.EL_le_R hx)

theorem normalizer_A_le_M : normalizer (m.A : Set G) ≤ m.M := by
  have hE1 : m.E ≠ ⊥ := by
    intro h
    have : m.r ^ 2 = 1 := by rw [← m.d.E_card, h]; exact Subgroup.card_bot
    rcases pow_eq_one_iff.1 this with h1 | h1
    · exact m.hr.ne_one h1
    · exact two_ne_zero h1
  exact m.d.normalizer_le_of_le_pGroup m.hC le_rfl hE1 (le_sup_right : m.E ≤ m.Z ⊔ m.E)
    (m.d.sylow.isPGroup.to_le m.A_le_R)

noncomputable def gE : ↥m.EL →* ↥m.M ⧸ m.KerKbar :=
  (QuotientGroup.mk' m.KerKbar).comp (Subgroup.inclusion m.EL_le_M)

noncomputable def W1 : Subgroup G := m.gE.ker.map m.EL.subtype

noncomputable def W2 : Subgroup G := (m.NK.comap m.gE).map m.EL.subtype

theorem W1_le : m.W1 ≤ m.A ⊓ m.L := Subgroup.map_subtype_le _

theorem W2_le : m.W2 ≤ m.A ⊓ m.L := Subgroup.map_subtype_le _

theorem exists_gE_conj {l : G} (hlM : l ∈ m.M) (hlE : l ∈ normalizer (m.EL : Set G)) (e : ↥m.EL) :
    ∃ e' : ↥m.EL, (e' : G) = l * e * l⁻¹ ∧
      m.gE e' = QuotientGroup.mk ⟨l, hlM⟩ * m.gE e * (QuotientGroup.mk ⟨l, hlM⟩)⁻¹ := by
  refine ⟨⟨l * e * l⁻¹, (mem_normalizer_iff.1 hlE e).1 e.2⟩, rfl, ?_⟩
  simp only [gE, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1

theorem mem_normalizer_W1 {l : G} (hlM : l ∈ m.M) (hlE : l ∈ normalizer (m.EL : Set G)) :
    l ∈ normalizer (m.W1 : Set G) := by
  refine mem_normalizer_of_forward_uc6 ?_
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨e', he'1, he'2⟩ := m.exists_gE_conj hlM hlE e
  refine ⟨e', ?_, he'1⟩
  have he1 : m.gE e = 1 := he
  show m.gE e' = 1
  rw [he'2, he1]
  simp

theorem mem_normalizer_W2 (hNK : m.NK.Normal) {l : G} (hlM : l ∈ m.M)
    (hlE : l ∈ normalizer (m.EL : Set G)) : l ∈ normalizer (m.W2 : Set G) := by
  refine mem_normalizer_of_forward_uc6 ?_
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨e', he'1, he'2⟩ := m.exists_gE_conj hlM hlE e
  refine ⟨e', ?_, he'1⟩
  show m.gE e' ∈ m.NK
  rw [he'2]
  exact hNK.conj_mem _ he _

theorem isElemAbelian_range_gE : CFSG.Open.IsElemAbelian m.r m.gE.range := by
  have hEL : CFSG.Open.IsElemAbelian m.r m.EL := (m.isElemAbelian_A).mono inf_le_left
  refine ⟨isMulCommutative_iff.2 ?_, ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show m.gE a * m.gE b = m.gE b * m.gE a
    rw [← map_mul, ← map_mul, hEL.1.is_comm.comm a b]
  · rintro _ ⟨e, rfl⟩
    rw [← map_pow]
    have : e ^ m.r = 1 := Subtype.ext (hEL.2 e e.2)
    rw [this, map_one]

theorem c631_of_K631 (hK : UCK.K631) (h620 : m.C620) (h621 : m.C621) (h625 : m.C625)
    (h629 : m.C629) : m.C631 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hNK := m.NK_normal
  have hMg : CFSG.Open.IsKGroup ↥m.M := Dat.standing.kProper.isKGroup m.M m.M_ne_top
  have hEcard : Nat.card ↥m.EL = m.r ^ 2 := m.card_A_inf_L h620
  have hr2 : 1 < m.r := m.hr.one_lt
  have hNinv : ∀ l ∈ m.L ⊓ normalizer (m.A : Set G), l ∈ m.M ∧ l ∈ normalizer (m.EL : Set G) :=
    fun l hl => ⟨m.normalizer_A_le_M hl.2, m.mem_normalizer_EL (Subgroup.le_normalizer hl.1) hl.2⟩
  rcases h621 m.W1 m.W1_le (fun l hl => m.mem_normalizer_W1 (hNinv l hl).1 (hNinv l hl).2) with h1 | h1
  · have hinj : Function.Injective m.gE := by
      rw [injective_iff_map_eq_one]
      intro e he
      have : (e : G) ∈ m.W1 := ⟨e, he, rfl⟩
      rw [h1] at this
      exact Subtype.ext (Subgroup.mem_bot.1 this)
    have hBcard : Nat.card m.gE.range = m.r ^ 2 := by
      rw [← hEcard]
      exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    have hBel := m.isElemAbelian_range_gE
    rcases h621 m.W2 m.W2_le
      (fun l hl => m.mem_normalizer_W2 hNK (hNinv l hl).1 (hNinv l hl).2) with h2 | h2
    · exfalso
      have hBN : m.gE.range ⊓ m.NK = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨⟨e, rfl⟩, hmem⟩
        have : (e : G) ∈ m.W2 := ⟨e, hmem, rfl⟩
        rw [h2] at this
        have he : e = 1 := Subtype.ext (Subgroup.mem_bot.1 this)
        rw [he, map_one]
        exact one_mem _
      have hle := hK (↥m.M ⧸ m.KerKbar) (hMg.quotient _) m.r m.hr m.d.odd m.NK hNK
        (m.NK_isSimple h629) (m.NK_not_comm h629) (m.NK_centralizer h629) (m.NK_pRank h625 h629)
        m.gE.range hBel hBN
      rw [hBcard] at hle
      nlinarith
    · exfalso
      have hBle : m.gE.range ≤ m.NK := by
        rintro _ ⟨e, rfl⟩
        have : (e : G) ∈ m.W2 := by rw [h2]; exact e.2
        obtain ⟨e', he', he'e⟩ := this
        have : e' = e := Subtype.ext he'e
        rw [← this]
        exact he'
      have h2le := CFSG.SectionRank.le_pRank hr2 hBle hBel hBcard
      have := m.NK_pRank h625 h629
      omega
  · show ⁅m.A ⊓ m.L, m.K⁆ ≤ m.U
    rw [Subgroup.commutator_le]
    intro e he k hk
    have : e ∈ m.W1 := by rw [h1]; exact he
    obtain ⟨e', he', rfl⟩ := this
    have he1 : m.gE e' = 1 := he'
    have he2 : Subgroup.inclusion m.EL_le_M e' ∈ m.KerKbar := by
      have h3 : (QuotientGroup.mk (Subgroup.inclusion m.EL_le_M e') : ↥m.M ⧸ m.KerKbar) = 1 := he1
      exact (QuotientGroup.eq_one_iff _).1 h3
    have := he2 k hk
    simpa [commutatorElement_def] using this

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
