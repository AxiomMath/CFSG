module

public import CFSG.Quasithin.EmptyFaithful.S153Ofour
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.Quasithin.EmptyFaithful.S142Basic
public import CFSG.Quasithin.EmptyFaithful.S153OfourFacts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

private theorem isMaxTwoLocal_conj {G : Type*} [Group G] {K : Subgroup G}
    (hK : quasithinIsMaxTwoLocal K) (g : G) :
    quasithinIsMaxTwoLocal (K.map (MulAut.conj g).toMonoidHom) := by
  have hmem : ∀ x, x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := fun x => by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  refine ⟨?_, fun H hH hle => ?_⟩
  · obtain ⟨P, hP, hP2, hPM⟩ := hK.1
    refine ⟨P.map (MulAut.conj g).toMonoidHom, ?_, hP2.map _, ?_⟩
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
    · rw [hPM]
      exact Subgroup.map_equiv_normalizer_eq P (MulAut.conj g)
  · have hH' : IsTwoLocal (H.map (MulAut.conj g⁻¹).toMonoidHom) := by
      obtain ⟨P, hP, hP2, hPH⟩ := hH
      refine ⟨P.map (MulAut.conj g⁻¹).toMonoidHom, ?_, hP2.map _, ?_⟩
      · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective]
      · rw [hPH]
        exact Subgroup.map_equiv_normalizer_eq P (MulAut.conj g⁻¹)
    have hKH : K ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro m hm
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
      apply hle
      rw [hmem]
      simpa [mul_assoc] using hm
    have heq := hK.2 _ hH' hKH
    ext x
    rw [hmem, ← heq, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem isSylowTwoOf_autI (h : Hyp153 G T Mc M) :
    IsSylowTwoOf (autI h.elemAbelian T) (autI h.elemAbelian M) :=
  B2F.isSylowTwoOf_autI h.elemAbelian h.le_normalizer h.isSylowTwoOf

theorem pCoreOf_ne_bot_of_le (h : Hyp153 G T Mc M) {X : Subgroup G} (hTX : T ≤ X) (hXM : X ≤ M) :
    pCoreOf 2 X ≠ ⊥ := by
  intro hbot
  obtain ⟨S, hS⟩ := h.qtfe.exists_sylow
  have hP : pCoreOf 2 M ≤ T := by
    have := pCoreOf_two_le_sylow M S (hS ▸ h.T_le)
    rwa [hS] at this
  have hle : pCoreOf 2 M ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 (hP.trans hTX) (hXM.trans (le_normalizer_pCoreOf 2 M))
      (pCoreOf_isPGroup 2 M)
  rw [hbot] at hle
  exact pCoreOf_ne_bot_of_isTwoLocal h.inM.1.1 (le_bot_iff.mp hle)

theorem dichotomy (h : Hyp153 G T Mc M) {X : Subgroup G} (hTX : T ≤ X) (hXM : X ≤ M) :
    autI h.elemAbelian X = autI h.elemAbelian T ∨ autI h.elemAbelian X = autI h.elemAbelian M := by
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  exact hS.maximal h.isSylowTwoOf_autI (autI_mono _ hTX) (autI_mono _ hXM)

theorem T_le_centralizer_Z (_h : Hyp153 G T Mc M) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.le_centralizer_iff.mp ((quasithinOmegaOneCenter_le_center T).trans inf_le_right)

theorem centralizer_VZ_le (_h : Hyp153 G T Mc M) :
    Subgroup.centralizer (VZ T M : Set G) ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.centralizer_le (le_conjClosure _ _)

theorem lemma_15_3_2_one (h : Hyp153 G T Mc M) : IsOFourPlusAction M (VZ T M) := h.ofour

theorem lemma_15_3_2_two (h : Hyp153 G T Mc M) :
    quasithinOmegaOneCenter T = VZ T M ⊓ Subgroup.centralizer (T : Set G) ∧
      Nat.card (quasithinOmegaOneCenter T) = 2 := by
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := h.Z_le_VZ
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
    (quasithinOmegaOneCenter_le_center T).trans inf_le_right
  have hCZ : VZ T M ⊓ Subgroup.centralizer (T : Set G) ≤ quasithinOmegaOneCenter T := by
    intro v hv
    exact Subgroup.subset_closure ⟨⟨h.VZ_le_T hv.1, hv.2⟩, h.elemAbelian.2 v hv.1⟩
  have hEq : quasithinOmegaOneCenter T = VZ T M ⊓ Subgroup.centralizer (T : Set G) :=
    le_antisymm (le_inf hZV hZC) hCZ
  refine ⟨hEq, ?_⟩
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  have hle : Nat.card (fixV (autI h.elemAbelian T)) ≤ 2 := hS.card_fixV_le_two h.isSylowTwoOf_autI
  have hc : Nat.card (fixV (autI h.elemAbelian T)) =
      Nat.card ↥(VZ T M ⊓ Subgroup.centralizer (T : Set G)) :=
    card_fixV_autI h.elemAbelian (h.T_le.trans h.le_normalizer)
  have hZ1 : Nat.card (quasithinOmegaOneCenter T) ≠ 1 := fun h1 =>
    h.qtfe.omegaOneCenter_ne_bot (Subgroup.card_eq_one.mp h1)
  have hpos : 0 < Nat.card (quasithinOmegaOneCenter T) := Nat.card_pos
  rw [hEq] at hZ1 hpos ⊢
  omega

theorem le_centralizer_Z_of_autI_eq_T (h : Hyp153 G T Mc M) {X : Subgroup G} (hXM : X ≤ M)
    (h1 : autI h.elemAbelian X = autI h.elemAbelian T) :
    X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer (hXM hx)
  have hφ : convI h.elemAbelian ⟨x, hxN⟩ ∈ autI h.elemAbelian T :=
    h1 ▸ convI_mem_autI h.elemAbelian hx hxN
  obtain ⟨g, hgT, hg⟩ := (mem_autI h.elemAbelian).1 hφ
  have hk : convI h.elemAbelian ((⟨x, hxN⟩ : Subgroup.normalizer (VZ T M : Set G)) * g⁻¹) = 1 := by
    rw [map_mul, map_inv, hg, mul_inv_cancel]
  have hk0 : x * (g : G)⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) :=
    (convI_eq_one_iff h.elemAbelian _).1 hk
  have hk' : x * (g : G)⁻¹ ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    h.centralizer_VZ_le hk0
  have : x = (x * (g : G)⁻¹) * g := by group
  rw [this]
  exact Subgroup.mul_mem _ hk' (h.T_le_centralizer_Z hgT)

theorem factor_of_autI_eq_M (h : Hyp153 G T Mc M) {X : Subgroup G} (hXM : X ≤ M)
    (h1 : autI h.elemAbelian X = autI h.elemAbelian M) :
    ∀ m ∈ M, ∃ x ∈ X, ∃ c ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G), m = x * c := by
  intro m hm
  have hmN : m ∈ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer hm
  have hφ : convI h.elemAbelian ⟨m, hmN⟩ ∈ autI h.elemAbelian X :=
    h1 ▸ convI_mem_autI h.elemAbelian hm hmN
  obtain ⟨g, hgX, hg⟩ := (mem_autI h.elemAbelian).1 hφ
  refine ⟨g, hgX, (g : G)⁻¹ * m, ⟨M.mul_mem (M.inv_mem (hXM hgX)) hm, ?_⟩, by group⟩
  have hk : convI h.elemAbelian ((g : Subgroup.normalizer (VZ T M : Set G))⁻¹ * ⟨m, hmN⟩) = 1 := by
    rw [map_mul, map_inv, hg, inv_mul_cancel]
  exact (convI_eq_one_iff h.elemAbelian _).1 hk

theorem isUniqueM_of_autI_eq_M (h : Hyp153 G T Mc M) {X : Subgroup G} (hTX : T ≤ X) (hXM : X ≤ M)
    (h1 : autI h.elemAbelian X = autI h.elemAbelian M) : IsUniqueM X M :=
  isUniqueM_of_isOrdMaximalIn h.mf.1 ⟨hTX, h.pCoreOf_ne_bot_of_le hTX hXM⟩ hXM
    (h.factor_of_autI_eq_M hXM h1)

theorem lemma_15_3_2_four (h : Hyp153 G T Mc M) {X : Subgroup G} (hTX : T ≤ X) (hXM : X ≤ M) :
    opResidual 2 X ≤ Subgroup.centralizer (VZ T M : Set G) ∨
      (autOn X (VZ T M) = autOn M (VZ T M) ∧ IsUniqueM X M) := by
  rcases h.dichotomy hTX hXM with h1 | h1
  · left
    rw [opResidual, Subgroup.closure_le]
    rintro x ⟨hxX, hxcop⟩
    have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer (hXM hxX)
    have hφ : convI h.elemAbelian ⟨x, hxN⟩ ∈ autI h.elemAbelian T :=
      h1 ▸ convI_mem_autI h.elemAbelian hxX hxN
    have hp2 : IsPGroup 2 (autI h.elemAbelian T) := h.isSylowTwoOf_autI.2.1
    obtain ⟨n, hn⟩ := hp2 ⟨_, hφ⟩
    have hord : orderOf (convI h.elemAbelian ⟨x, hxN⟩) ∣ orderOf x := by
      have := orderOf_map_dvd (convI h.elemAbelian) (⟨x, hxN⟩ : Subgroup.normalizer (VZ T M : Set G))
      rwa [Subgroup.orderOf_mk] at this
    have hcop' : Nat.Coprime (orderOf (convI h.elemAbelian ⟨x, hxN⟩)) 2 :=
      Nat.Coprime.coprime_dvd_left hord hxcop
    have hdvd : orderOf (convI h.elemAbelian ⟨x, hxN⟩) ∣ 2 ^ n := by
      have := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hn)
      simpa using this
    have h1' : orderOf (convI h.elemAbelian ⟨x, hxN⟩) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n hcop') hdvd
    have : convI h.elemAbelian ⟨x, hxN⟩ = 1 := orderOf_eq_one_iff.mp h1'
    exact (convI_eq_one_iff h.elemAbelian ⟨x, hxN⟩).1 this
  · right
    exact ⟨h1, h.isUniqueM_of_autI_eq_M hTX hXM h1⟩

theorem lemma_15_3_2_five (h11 : StageLemma14111) (h : Hyp153 G T Mc M) :
    IsOrdMaximal T M ∧ ∀ K : Subgroup G, InM T K → OrdLE T K M := by
  refine ⟨h.mf.1, fun K hK => ?_⟩
  by_cases hKc : K = Mc
  · rw [hKc]
    exact ordLE_mc_of_card_two h.qtfe (h11 G T Mc h.qtfe) h.mf h.lemma_15_3_2_two.2
  · exact h.mf.2.2 K hK hKc

theorem lemma_15_3_2_three (h11 : StageLemma14111) (h : Hyp153 G T Mc M) {K : Subgroup G} :
    InM T K ↔ K = M ∨ K = Mc := by
  constructor
  · intro hK
    have hKM := (h.lemma_15_3_2_five h11).2 K hK
    have hTX : T ≤ M ⊓ K := le_inf h.T_le hK.2
    have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Mc :=
      h.qtfe.centralizer_le_mc
    rcases h.dichotomy hTX inf_le_left with h1 | h1
    · right
      have hXC := h.le_centralizer_Z_of_autI_eq_T inf_le_left h1
      have hKle : K ≤ Mc := by
        intro k hk
        obtain ⟨a, ha, c, hc, rfl⟩ := hKM k hk
        exact Mc.mul_mem (hCZ (hXC (Subgroup.mem_inf.mpr ⟨ha.2, ha.1⟩)))
          (hCZ (Subgroup.centralizer_le (le_conjClosure (quasithinOmegaOneCenter T) K) hc.2))
      exact (hK.1.2 Mc h.qtfe.mc_max.1 hKle).symm
    · left
      exact ((h.isUniqueM_of_autI_eq_M hTX inf_le_left h1).2 K ⟨hK.1, inf_le_right⟩)
  · rintro (rfl | rfl)
    · exact h.inM
    · exact h.qtfe.inM_mc

theorem lemma_15_3_2_six (h11 : StageLemma14111) (h : Hyp153 G T Mc M) :
    Subgroup.normalizer (T : Set G) ≤ M ∧
      ∀ H : Subgroup G, IsHStar T M H → MinParabolic H T (H ⊓ M) := by
  have hN : Subgroup.normalizer (T : Set G) ≤ M := by
    intro g hg
    have hNZ := normalizer_le_normalizer_quasithinOmegaOneCenter T
    have hZ2 := h.lemma_15_3_2_two.2
    have hNC : Subgroup.normalizer (T : Set G) ≤
        Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      hNZ.trans (normalizer_le_centralizer_of_card_two hZ2)
    set Mg : Subgroup G := M.map (MulAut.conj g).toMonoidHom with hMg
    have hmemMg : ∀ x, x ∈ Mg ↔ g⁻¹ * x * g ∈ M := fun x => by
      rw [hMg, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have hMgloc : quasithinIsMaxTwoLocal Mg := isMaxTwoLocal_conj h.inM.1 g
    have hTMg : T ≤ Mg := by
      intro t ht
      rw [hmemMg]
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) t).mp ht
      simp only [inv_inv] at this
      exact h.T_le this
    rcases (h.lemma_15_3_2_three h11).1 ⟨hMgloc, hTMg⟩ with hMgM | hMgC
    · have hgM : ∀ m ∈ M, g * m * g⁻¹ ∈ M := fun m hm => by
        rw [← hMgM, hmemMg]
        simpa [mul_assoc] using hm
      have hgM' : ∀ m ∈ M, g⁻¹ * m * g⁻¹⁻¹ ∈ M := fun m hm => by
        rw [inv_inv, ← hmemMg m]
        rwa [hMgM]
      have hgZ : ∀ z ∈ quasithinOmegaOneCenter T, g * z * g⁻¹ ∈ quasithinOmegaOneCenter T :=
        fun z hz => (Subgroup.mem_normalizer_iff.mp (hNZ hg) z).mp hz
      have hgZ' : ∀ z ∈ quasithinOmegaOneCenter T, g⁻¹ * z * g⁻¹⁻¹ ∈ quasithinOmegaOneCenter T :=
        fun z hz => (Subgroup.mem_normalizer_iff.mp (hNZ (inv_mem hg)) z).mp hz
      have hgV : g ∈ Subgroup.normalizer (VZ T M : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        refine ⟨conj_mem_conjClosure hgZ hgM, fun hx => ?_⟩
        have := conj_mem_conjClosure hgZ' hgM' hx
        show x ∈ conjClosure (quasithinOmegaOneCenter T) M
        simpa [mul_assoc] using this
      exact (h.isHv_of_inM' h.inM).symm.le hgV
    · exfalso
      have hgMc : g ∈ Mc := h.qtfe.centralizer_le_mc (hNC hg)
      have hMleMc : M ≤ Mc := by
        intro m hm
        have h1 : g * m * g⁻¹ ∈ Mc := by
          rw [← hMgC, hmemMg]
          simpa [mul_assoc] using hm
        have := Mc.mul_mem (Mc.mul_mem (Mc.inv_mem hgMc) h1) hgMc
        simpa [mul_assoc] using this
      exact h.ne_mc (h.inM.1.2 Mc h.qtfe.mc_max.1 hMleMc).symm
  refine ⟨hN, fun H hH => ?_⟩
  obtain ⟨S, hS⟩ := h.qtfe.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ h.T_le
  have hH' : IsHStar (S : Subgroup G) M H := hS ▸ hH
  refine ⟨?_, hH.not_le_normalizer hN, ?_⟩
  · have := isSylowTwoOf_of_sylow S (hS ▸ hH.1.1)
    rwa [hS] at this
  · have := hH'.isUniqueMaxOver S hSM
    rwa [hS] at this

theorem T_le_normalizer_C₂ (_h : Hyp153 G T Mc M) {C₂ : Subgroup G} (hC : Lemma14111Concl T Mc C₂) :
    T ≤ Subgroup.normalizer (C₂ : Set G) := by
  have h1 : T ≤ Subgroup.normalizer (baum T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  exact h1.trans (normalizer_le_normalizer_of_characteristic_subgroupOf hC.2.1 hC.2.2.1)

theorem lemma_15_3_3_one (h : Hyp153 G T Mc M) {C₂ : Subgroup G} (hC : Lemma14111Concl T Mc C₂) :
    IsUniqueM (M ⊓ Subgroup.normalizer (C₂ : Set G)) M := by
  have hfac : ∀ m ∈ M, ∃ c ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G),
      ∃ n ∈ M ⊓ Subgroup.normalizer (C₂ : Set G), m = c * n := by
    rcases hC.2.2.2 M h.inM with hfac | ⟨heq, -⟩
    · exact hfac
    · exact absurd heq h.ne_mc
  have hTX : T ≤ M ⊓ Subgroup.normalizer (C₂ : Set G) := le_inf h.T_le (h.T_le_normalizer_C₂ hC)
  refine isUniqueM_of_isOrdMaximalIn h.mf.1 ⟨hTX, h.pCoreOf_ne_bot_of_le hTX inf_le_left⟩
    inf_le_left fun m hm => ?_
  obtain ⟨c, hc, n, hn, rfl⟩ := hfac m hm
  refine ⟨n, hn, n⁻¹ * c * n, ⟨?_, ?_⟩, by group⟩
  · exact M.mul_mem (M.mul_mem (M.inv_mem hn.1) hc.1) hn.1
  · have hnV : n ∈ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer hn.1
    have hcen : c ∈ Subgroup.centralizer (VZ T M : Set G) := hc.2
    show n⁻¹ * c * n ∈ Subgroup.centralizer (VZ T M : Set G)
    rw [Subgroup.mem_centralizer_iff] at hcen ⊢
    intro v hv
    have hv' : n * v * n⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hnV v).mp hv
    have h1 := hcen _ hv'
    calc v * (n⁻¹ * c * n) = n⁻¹ * ((n * v * n⁻¹) * c) * n := by group
      _ = n⁻¹ * (c * (n * v * n⁻¹)) * n := by rw [h1]
      _ = n⁻¹ * c * n * v := by group

theorem lemma_15_3_3_two (_h : Hyp153 G T Mc M) {C₂ : Subgroup G} (hC : Lemma14111Concl T Mc C₂)
    (hN : Subgroup.normalizer (C₂ : Set G) ≤ M) {S : Subgroup G} (hBS : baum T ≤ S) (hST : S ≤ T) :
    baum T = baum S ∧ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (baum S : Set G) ∧
      Subgroup.normalizer (baum S : Set G) ≤ M := by
  have hb : baum T = baum S := baum_eq_of_le hBS hST
  refine ⟨hb, normalizer_le_normalizer_baum S, ?_⟩
  rw [← hb]
  exact (normalizer_le_normalizer_of_characteristic_subgroupOf hC.2.1 hC.2.2.1).trans hN

theorem lemma_15_3_4 (h11 : StageLemma14111) (h : Hyp153 G T Mc M) :
    Mc = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have hZ2 := h.lemma_15_3_2_two.2
  have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Mc :=
    h.qtfe.centralizer_le_mc
  have hle := (h.lemma_15_3_2_five h11).2 Mc h.qtfe.inM_mc
  have hUZ : VZ T Mc = quasithinOmegaOneCenter T := by
    by_contra hne
    have hlt : quasithinOmegaOneCenter T < VZ T Mc :=
      lt_of_le_of_ne (le_conjClosure _ _) (Ne.symm hne)
    have hTX : T ≤ M ⊓ Mc := le_inf h.T_le h.qtfe.t_le_mc
    have hUX : VZ T Mc ≤ conjClosure (quasithinOmegaOneCenter T) (M ⊓ Mc) := by
      refine conjClosure_le fun k hk z hz => ?_
      obtain ⟨a, ha, c, hc, rfl⟩ := hle k hk
      have hcz : c * z = z * c :=
        (Subgroup.mem_centralizer_iff.mp hc.2 z (le_conjClosure _ _ hz)).symm
      have : a * c * z * (a * c)⁻¹ = a * z * a⁻¹ := by
        calc a * c * z * (a * c)⁻¹ = a * (c * z) * c⁻¹ * a⁻¹ := by group
          _ = a * z * a⁻¹ := by rw [hcz]; group
      rw [this]
      exact mem_conjClosure ⟨ha.2, ha.1⟩ hz
    rcases h.dichotomy hTX inf_le_left with h1 | h1
    ·
      have hXC := h.le_centralizer_Z_of_autI_eq_T inf_le_left h1
      have : conjClosure (quasithinOmegaOneCenter T) (M ⊓ Mc) ≤ quasithinOmegaOneCenter T := by
        refine conjClosure_le fun x hx z hz => ?_
        have := Subgroup.mem_centralizer_iff.mp (hXC hx) z hz
        rw [← this, mul_inv_cancel_right]
        exact hz
      exact absurd (hUX.trans this) (not_le_of_gt hlt)
    ·
      have hU := h.isUniqueM_of_autI_eq_M hTX inf_le_left h1
      exact h.ne_mc (hU.2 Mc ⟨h.qtfe.mc_max, inf_le_right⟩).symm
  have hHv := h.isHv_of_inM' h.qtfe.inM_mc
  apply le_antisymm _ hCZ
  calc Mc = Subgroup.normalizer (VZ T Mc : Set G) := hHv
    _ = Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by rw [hUZ]
    _ ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      normalizer_le_centralizer_of_card_two hZ2

end Hyp153

end CFSG.Quasithin
