module

public import CFSG.Quasithin.EmptyFaithful.R3c8Grp
public import CFSG.Quasithin.EmptyFaithful.R3c8Lie
public import CFSG.Quasithin.EmptyFaithful.R3c5Three

public section

namespace CFSG.Quasithin.R3c8

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Ctx

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : ⁅H, K⁆ ≤ (⁅H, K⁆).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro h hh k hk
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj g).toMonoidHom ⁅h, k⁆ = ⁅(MulAut.conj g) h, (MulAut.conj g) k⁆ :=
      map_commutatorElement (MulAut.conj g).toMonoidHom h k
    rw [e]
    refine Subgroup.commutator_mem_commutator ?_ ?_
    · exact (Subgroup.mem_normalizer_iff.mp hH h).mp hh
    · exact (Subgroup.mem_normalizer_iff.mp hK k).mp hk
  exact hle hx

theorem V₂_le_Sgp153 {T Mc M V₁ V₂ : Subgroup G} {t : G} (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) : V₂ ≤ Sgp153 T V₁ := by
  intro v hv
  refine ⟨h.VZ_le_T (D.le₂ hv), A4.mem_normalizer_of_conj_mem fun k hk => ?_⟩
  have hc := congrArg Subtype.val
    (h.elemAbelian.1.is_comm.comm ⟨v, D.le₂ hv⟩ ⟨k, D.le₁ hk⟩)
  have : v * k * v⁻¹ = k := by
    have h1 : v * k = k * v := hc
    rw [h1]
    group
  rw [this]
  exact hk

theorem MI_le_normalizer_V₂ {T Mc M V₁ V₂ Yp I : Subgroup G} {t : G}
    (hh : Hyp15310 G T Mc M V₁ V₂ Yp t) (hb1 : ⁅V₁, Yp⁆ = ⊥) (hb2 : ⁅V₂, Yp⁆ = V₂)
    (hnorm : I ⊓ Subgroup.normalizer (Yp : Set G) = M ⊓ I) :
    M ⊓ I ≤ Subgroup.normalizer (V₂ : Set G) := by
  have hYpM : Yp ≤ M := hh.Yp_le_Y153.trans (Y153_le Mc M)
  have hYpC : Yp ≤ Subgroup.centralizer (V₁ : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hb1
  have hVY : ⁅VZ T M, Yp⁆ = V₂ := by
    apply le_antisymm
    · rw [← hh.decomp.comm₂]
      exact Subgroup.commutator_mono le_rfl (le_inf hYpM hYpC)
    · calc V₂ = ⁅V₂, Yp⁆ := hb2.symm
        _ ≤ ⁅VZ T M, Yp⁆ := Subgroup.commutator_mono hh.decomp.le₂ le_rfl
  intro m hm
  have h1 : m ∈ Subgroup.normalizer (VZ T M : Set G) := hh.hyp.le_normalizer hm.1
  have h2 : m ∈ Subgroup.normalizer (Yp : Set G) := by
    have : m ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [hnorm]; exact hm
    exact this.2
  have := mem_normalizer_commutator h1 h2
  rwa [hVY] at this

end Ctx

section Main

variable {G : Type} [Group G] [Finite G]

theorem charTwo_borel_of_cent {L P : Subgroup G} (hP : IsSylowTwoOf P L)
    (hcent : ∀ x ∈ L, (∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ centerOf L) → x ∈ P) :
    CharTwo (L ⊓ Subgroup.normalizer (P : Set G)) := by
  intro b hb
  rw [SBc2.pCoreOf_borel hP] at hb ⊢
  obtain ⟨hbB, hbC⟩ := hb
  refine hcent b hbB.1 fun p hp' => ?_
  have h := Subgroup.mem_centralizer_iff.mp hbC p hp'
  have e : b * p * b⁻¹ * p⁻¹ = 1 := by
    rw [← h]
    group
  rw [e]
  exact Subgroup.one_mem _

theorem input15343Diag_holds (h113 : StageLemma14113)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) : R3c5.Input15343Diag := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hL0 hr hfam hy
  obtain ⟨y, hyY, hy3, hyL⟩ := hy
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hYL : Yp ≤ Subgroup.normalizer (L : Set G) :=
    S153D.Yp_le_normalizer h37 h38 hh c.inH hLc
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := by
    have := le_normalizer_conjClosure L (Sgp153 T V₁)
    rwa [← hL0] at this
  have hXL : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := sup_le hYL hSL
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  obtain ⟨φ, -, hker⟩ := c.facts25.s3
  have hQR : Sgp153 T V₁ ⊓ L ≤ R153 T V₁ Yp :=
    inf_le_pCore_of_s3 hXL le_sup_right le_sup_left hSyl.2.1 (pCoreOf_isPGroup 2 _) φ hker hyY hy3 hyL
  have hREq := c.facts25.R_eq
  have hRS : R153 T V₁ Yp ≤ Sgp153 T V₁ := hREq ▸ inf_le_left
  have hQRL : Sgp153 T V₁ ⊓ L = R153 T V₁ Yp ⊓ L :=
    le_antisymm (le_inf hQR inf_le_right) (inf_le_inf_right _ hRS)
  have hXR : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (R153 T V₁ Yp : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hXQ : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := by
    rw [hQRL]
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hXR hg, hXL hg⟩
  have hpkg := borelPkg_of_family c.c33.center_eq hr hfam
  obtain ⟨hcent, hrig⟩ := borelLift_of_pkg c.c33.quasisimple c.c33.center_eq hQsyl hpkg
  set Q : Subgroup G := Sgp153 T V₁ ⊓ L with hQdef
  have hChar : CharTwo (L ⊓ Subgroup.normalizer (Q : Set G)) := charTwo_borel_of_cent hQsyl hcent
  have hBX : Yp ⊔ Sgp153 T V₁ ≤
      Subgroup.normalizer ((L ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) : Set G) :=
    SBc2.le_normalizer_borel hXL hXQ
  have hBMI : L ⊓ Subgroup.normalizer (Q : Set G) ≤ M ⊓ I :=
    c.c33.inv_le _ (inf_le_left.trans hL0.le) hBX hChar
  set B : Subgroup G := L ⊓ Subgroup.normalizer (Q : Set G) with hBdef
  have hQB : IsSylowTwoOf Q B :=
    A4.isSylowTwoOf_mono hQsyl (le_inf hQsyl.1 Subgroup.le_normalizer) inf_le_left
  by_cases h3 : 3 ∣ Nat.card ↥B
  ·
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 h3
    have hbG : orderOf (b : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hb
    have hbY : (b : G) ∈ Yp := by
      rw [o.a_eq]
      exact Subgroup.subset_closure ⟨hBMI b.2, 1, by simpa using hbG⟩
    obtain ⟨a, hcard⟩ : ∃ a : ℕ, Nat.card ↥Yp = 3 * 2 ^ a := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Yp)
      obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥Yp)).exists_card_eq
      refine ⟨a, ?_⟩
      have h2 : Nat.card (↥Yp ⧸ CFSG.Open.pCore 2 ↥Yp) = 3 := o.a_ord
      rw [h1, ha, h2]
    have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
    exact hyL (Subgroup.mem_sup_left
      (mem_of_card_three_mul_two_pow hYL hcard hbY b.2.1 hbG hyY hy3'))
  ·
    have hV2S : V₂ ≤ Sgp153 T V₁ := V₂_le_Sgp153 hh.hyp hh.decomp
    have hBN₂ : B ≤ Subgroup.normalizer (V₂ : Set G) :=
      hBMI.trans (MI_le_normalizer_V₂ hh o.b_V1 o.b_V2.1 c.facts.norm_eq)
    have hQC : Q ≤ Subgroup.centralizer (V₂ : Set G) := hQR.trans (hREq ▸ inf_le_right)
    have hBC : B ≤ Subgroup.centralizer (V₂ : Set G) :=
      le_centralizer_of_odd hBN₂ hh.decomp.card₂ hQB hQC h3
    have hVC : ∀ v ∈ V₂, v ∈ Subgroup.centralizer (L : Set G) := by
      intro v hv
      refine hrig v (hSL (hV2S hv)) ?_ ?_
      · have := hh.hyp.elemAbelian.2 v (hh.decomp.le₂ hv)
        rw [← sq]
        exact this
      · intro b hb
        exact Subgroup.mem_centralizer_iff.mp (hBC hb) v hv
    have hLC : L ≤ Subgroup.centralizer (V₂ : Set G) := fun l hl =>
      Subgroup.mem_centralizer_iff.mpr fun v hv =>
        (Subgroup.mem_centralizer_iff.mp (hVC v hv) l hl).symm
    have hLM : L ≤ M := hLC.trans ((Subgroup.centralizer_le_normalizer _).trans
      (Hyp153.normalizer_V_le h113 hh.hyp hh.decomp c.facts25.case_two.1).2)
    exact c.c33.not_le hLM

end Main

end CFSG.Quasithin.R3c8
