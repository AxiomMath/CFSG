module

public import CFSG.Quasithin.H13.U3S13227P
public import CFSG.Quasithin.H13.U3C137Z

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_mul_decomp (S : A6.Setting134 G T L V) {x : G} (hx : x ∈ L ⊔ T) :
    ∃ l ∈ L, ∃ t ∈ T, x = l * t := by
  have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T S.T_le_NL
  have hx' : x ∈ (L : Set G) * (T : Set G) := by rw [← hmul]; exact hx
  obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨l, hl, t, ht, rfl⟩

theorem s134_mem_NV1_iff (S : A6.Setting134 G T L V) (g : ↥(normalizer (V : Set G))) :
    (g : G) ∈ normalizer (fsuV1 T V : Set G) ↔ Pres45 (S.frame.ρ g) :=
  ⟨s134_pres45 S g, fun h => s134_mem_normalizer_V1_of_P1 S g (inP1_of_pres45 _ h)⟩

theorem stab45_pres45 : ∀ σ ∈ stab45List, Pres45 σ := by decide +kernel

theorem s134_NLTV1_max (S : A6.Setting134 G T L V) (H : Subgroup G)
    (hMH : (L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G) ≤ H) (hHX : H ≤ L ⊔ T) :
    H = (L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G) ∨ H = L ⊔ T := by
  set M := (L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G) with hM
  by_cases hHM : H ≤ M
  · exact Or.inl (le_antisymm hHM hMH)
  right
  obtain ⟨h, hhH, hhM⟩ := IsConcreteLE.not_le_iff_exists.1 hHM
  obtain ⟨l, hl, t, ht, rfl⟩ := s134_mul_decomp S (hHX hhH)
  have htM : t ∈ M := ⟨mem_sup_right ht, T_le_normalizer_fsuV1 T V ht⟩
  have hlH : l ∈ H := by
    have := H.mul_mem hhH (H.inv_mem (hMH htM))
    rwa [mul_inv_cancel_right] at this
  have hlM : l ∉ M := fun h' => hhM (M.mul_mem h' htM)
  set lN : ↥(normalizer (V : Set G)) := ⟨l, S.frame.L_le hl⟩ with hlN
  have hs1 : Perm.sign (S.frame.ρ lN) = 1 :=
    Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨lN, hl, rfl⟩)
  have hsC : S.frame.ρ lN ∉ stab45 := fun hmem =>
    hlM ⟨mem_sup_left hl, (s134_mem_NV1_iff S lN).2 (stab45_pres45 _ hmem)⟩
  set Y : Subgroup (Perm (Fin 6)) :=
    ((H ⊓ L).subgroupOf (normalizer (V : Set G))).map S.frame.ρ with hY
  have hCY : stab45 ≤ Y := by
    intro σ hσ
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 (stab45_le_alt hσ)
    have hgM : (g : G) ∈ M := ⟨mem_sup_left hgL,
      (s134_mem_NV1_iff S g).2 (by rw [hg]; exact stab45_pres45 σ hσ)⟩
    exact ⟨g, mem_subgroupOf.2 ⟨hMH hgM, hgL⟩, hg⟩
  have hsY : S.frame.ρ lN ∈ Y := ⟨lN, mem_subgroupOf.2 ⟨hlH, hl⟩, rfl⟩
  have hA := alt6_le_of_overgroup24 card_stab45 stab45_le_alt hCY hsY hs1 hsC
  refine le_antisymm hHX (sup_le (fun l' hl' => ?_) fun t' ht' =>
    hMH ⟨mem_sup_right ht', T_le_normalizer_fsuV1 T V ht'⟩)
  set l'N : ↥(normalizer (V : Set G)) := ⟨l', S.frame.L_le hl'⟩ with hl'N
  obtain ⟨g, hg, hgρ⟩ := hA ((S.frame.image_L _).1 ⟨l'N, hl', rfl⟩)
  have hgHL := mem_subgroupOf.1 hg
  have hk : S.frame.ρ (g⁻¹ * l'N) = 1 := by rw [map_mul, map_inv, hgρ, inv_mul_cancel]
  have hkM : ((g⁻¹ * l'N : ↥(normalizer (V : Set G))) : G) ∈ M := by
    refine ⟨mem_sup_left ?_, (s134_mem_NV1_iff S _).2 (by rw [hk]; decide)⟩
    simpa [hl'N] using L.mul_mem (L.inv_mem hgHL.2) hl'
  have := H.mul_mem hgHL.1 (hMH hkM)
  simpa [hl'N] using this

theorem s134_NLTV1_lt (S : A6.Setting134 G T L V) :
    (L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G) < L ⊔ T := by
  refine lt_of_le_of_ne inf_le_left fun h => ?_
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L (swap 0 4 * swap 1 5)).2
    (Perm.mem_alternatingGroup.2 (by decide))
  have hgN : (g : G) ∈ normalizer (fsuV1 T V : Set G) := (h.symm.le (mem_sup_left hgL)).2
  have := (s134_mem_NV1_iff S g).1 hgN
  rw [hg] at this
  revert this
  decide

theorem s134_NLV1_le_L1T (S : A6.Setting134 G T L V) :
    L ⊓ normalizer (fsuV1 T V : Set G) ≤ L₁Of L (fsuV1 T V) ⊔ T := by
  have hTN : T ⊓ L ≤ L ⊓ normalizer (fsuV1 T V : Set G) := fun t ht =>
    ⟨ht.2, T_le_normalizer_fsuV1 T V ht.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ L) (L ⊓ normalizer (fsuV1 T V : Set G)) :=
    C1GN.isSylowTwoOf_of_le (s134_sylow_TL S) hTN inf_le_left
  have h := C1Pack12.oTwoUpper_sup_eq_of_sylow hsyl
  rw [← h, ← oTwoRes_eq_oTwoUpper]
  exact sup_le_sup le_rfl inf_le_left

theorem s134_L1T_eq_NLTV1 (S : A6.Setting134 G T L V) :
    L₁Of L (fsuV1 T V) ⊔ T = (L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G) := by
  apply le_antisymm
  · exact le_inf (sup_le_sup_right ((oTwoRes_le _).trans inf_le_left) T)
      (sup_le ((oTwoRes_le _).trans inf_le_right) (T_le_normalizer_fsuV1 T V))
  · rintro x ⟨hx, hxN⟩
    obtain ⟨l, hl, t, ht, rfl⟩ := s134_mul_decomp S hx
    have hlN : l ∈ normalizer (fsuV1 T V : Set G) := by
      have := (normalizer (fsuV1 T V : Set G)).mul_mem hxN
        ((normalizer (fsuV1 T V : Set G)).inv_mem (T_le_normalizer_fsuV1 T V ht))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (s134_NLV1_le_L1T S ⟨hl, hlN⟩) (mem_sup_right ht)

theorem s134_reduced (S : A6.Setting134 G T L V) :
    IsTwoReducedIn (L ⊔ T) V := by
  have hLTV : L ⊔ T ≤ normalizer (V : Set G) := sup_le S.frame.L_le S.frame.T_le
  refine isTwoReducedIn_of_comm (S.V_le_T.trans le_sup_right) hLTV (s134_elemAbelian_V S)
    fun g hg hcomm => ?_
  refine (s134_rho_eq_one_iff S ⟨g, hLTV hg⟩).1 ?_
  by_contra hne
  obtain ⟨τ, hτR, hτ4⟩ := redWit _ hne
  obtain ⟨l, hlL, rfl⟩ :=
    (S.frame.image_L τ).2 (Perm.mem_alternatingGroup.2 (redList_sign τ hτR))
  obtain ⟨k, hk⟩ := hcomm l hlL
  apply hτ4
  have h1 : S.frame.ρ ((⟨g, hLTV hg⟩ * l * ⟨g, hLTV hg⟩⁻¹ * l⁻¹) ^ 2 ^ k) = 1 :=
    (s134_rho_eq_one_iff S _).2 (by simpa using hk)
  rw [map_pow, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  exact pow_four_of_pow_two_pow h1

theorem s134_card_autOn_ne (S : A6.Setting134 G T L V) :
    Nat.card ↥(autOn (L ⊔ T) V) ≠ 12096 := by
  intro h
  set H := (L ⊔ T).subgroupOf (normalizer (V : Set G)) with hH
  let f : ↥H →* MulAut ↥V := (conjAct V).comp H.subtype
  let g : ↥H →* Perm (Fin 6) := S.frame.ρ.comp H.subtype
  have hf : f.range = autOn (L ⊔ T) V := by
    rw [MonoidHom.range_comp, range_subtype]
    rfl
  have hker : g.ker ≤ f.ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (s134_conjAct_eq_one_iff_rho S _).2 hx
  have h1 : f.ker.index ∣ g.ker.index := index_dvd_of_le hker
  rw [index_ker, index_ker, hf, h] at h1
  have h2 : Nat.card g.range ∣ 720 := by
    have := card_subgroup_dvd_card g.range
    have h720 : Nat.card (Perm (Fin 6)) = 720 := by rw [Nat.card_perm]; simp [Nat.factorial]
    rwa [h720] at this
  have := h1.trans h2
  norm_num at this

theorem s134_not_isHatBlock (S : A6.Setting134 G T L V)
    (hhat : IsHatA6 L) : ¬ H13.IsHatA6Block L := by
  rintro ⟨hshort, -, -, hCU⟩
  obtain ⟨-, -, -, -, -, hirr⟩ := hshort
  have hcomm : ⁅V, L⁆ = V := S.irr.2.2.2.1
  have hVL : V ≤ L := by
    rw [← hcomm, commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    have hvl : v * l * v⁻¹ ∈ L :=
      (mem_normalizer_iff.mp (S.T_le_NL (S.V_le_T hv)) l).mp hl
    exact L.mul_mem hvl (L.inv_mem hl)
  have hVQ : V ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 hVL S.frame.L_le S.isPGroup_V
  have hVU : V ≤ QuasithinUnique.blockU L := by
    rw [← hcomm]
    exact commutator_mono hVQ le_rfl
  set W : Subgroup G := QuasithinUnique.blockU L ⊓ centralizer (o2Z L : Set G) with hW
  have hZW : QuasithinUnique.blockZ L ≤ W :=
    le_inf inf_le_left (inf_le_right.trans (centralizer_le o2Z_le_L))
  have hLW : L ≤ normalizer (W : Set G) := by
    refine F7.le_normalizer_inf ?_ ?_
    · exact A5.le_normalizer_commutator (le_normalizer_pCoreOf 2 L) le_normalizer
    · exact fun l hl => mem_normalizer_centralizer_of_mem
        (normalizer_L_le_o2Z (le_normalizer hl))
  have hVW : V ≤ W := le_inf hVU (le_centralizer_iff.mp (s134_o2Z_le_centralizer S))
  rcases hirr W hZW inf_le_left hLW with h | h
  · have hVC : V ≤ V ⊓ centralizer (L : Set G) :=
      le_inf le_rfl (hVW.trans (h.le.trans inf_le_right))
    exact (lt_irrefl _ (S.irr.2.2.2.2.1.trans_le hVC))
  · obtain ⟨c, hc, -, hcO, -⟩ := exists_l0_c hhat.2.1
    have hcZ : c ∈ o2Z L := oTwoRes_le _ hc
    have hUC : QuasithinUnique.blockU L ≤ centralizer (o2Z L : Set G) :=
      h.symm.le.trans inf_le_right
    have hcU : c ∈ centralizer (QuasithinUnique.blockU L : Set G) :=
      le_centralizer_iff.mp hUC hcZ
    exact hcO (hCU.le ⟨o2Z_le_L hcZ, hcU⟩)

theorem mem_ker_altDn_iff {x : P6} :
    x ∈ (FFModel.altDn 6).ker ↔ x = 1 ∨ x = G6.allOnes 6 := by
  show x ∈ zpowers (G6.allOnes 6) ⊓ G6.coreMod 6 ↔ _
  rw [mem_inf, B5FinPerm.mem_zpowers_allOnes_iff]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rcases h with rfl | rfl
    · exact one_mem _
    · exact allOnes_mem_core

theorem permAct_mem_ker (γ : Perm (Fin 6)) {m : P6}
    (hm : m ∈ zpowers (G6.allOnes 6) ⊓ G6.coreMod 6) :
    G6.permAct 6 γ m ∈ zpowers (G6.allOnes 6) ⊓ G6.coreMod 6 := by
  have hm' : m = 1 ∨ m = G6.allOnes 6 := mem_ker_altDn_iff.1 hm
  refine mem_ker_altDn_iff.2 ?_
  rcases hm' with rfl | rfl
  · left; rw [map_one]
  · right; rw [permAct_allOnes]

theorem coreAct_mk_eq (γ : Perm (Fin 6)) {a b : ↥(G6.coreMod 6)}
    (h : (QuotientGroup.mk a : ↥(G6.coreMod 6) ⧸
      (zpowers (G6.allOnes 6) ⊓ G6.coreMod 6).subgroupOf (G6.coreMod 6)) = QuotientGroup.mk b) :
    (QuotientGroup.mk (G6.coreAct 6 γ a) : ↥(G6.coreMod 6) ⧸
      (zpowers (G6.allOnes 6) ⊓ G6.coreMod 6).subgroupOf (G6.coreMod 6)) =
        QuotientGroup.mk (G6.coreAct 6 γ b) := by
  rw [QuotientGroup.eq, mem_subgroupOf] at h ⊢
  rw [← map_inv, ← map_mul, G6.coreAct_coe]
  exact permAct_mem_ker γ h

theorem s134_alternatingNatural (S : A6.Setting134 G T L V) :
    ∃ _ : IsMulCommutative ↥V, AlternatingNatural (V := ↥V) (autOn L V) ⊤
      ((centralizer (L : Set G)).subgroupOf V) 6 := by
  classical
  have hab : IsMulCommutative ↥V := (s134_elemAbelian_V S).1
  refine ⟨hab, ?_⟩
  have hlift : ∀ σ : ↥(alternatingGroup (Fin 6)), ∃ g : ↥(normalizer (V : Set G)),
      (g : G) ∈ L ∧ S.frame.ρ g = σ := fun σ => (S.frame.image_L σ).2 σ.2
  choose lift hliftL hliftρ using hlift
  have hmemA : ∀ σ, conjAct V (lift σ) ∈ autOn L V := fun σ =>
    ⟨lift σ, mem_subgroupOf.2 (hliftL σ), rfl⟩
  let π : ↥(alternatingGroup (Fin 6)) →* ↥(autOn L V) :=
    MonoidHom.mk' (fun σ => ⟨conjAct V (lift σ), hmemA σ⟩) fun σ τ => by
      apply Subtype.ext
      show conjAct V (lift (σ * τ)) = conjAct V (lift σ) * conjAct V (lift τ)
      rw [← map_mul, s134_conjAct_eq_iff_rho S, map_mul, hliftρ, hliftρ, hliftρ]
      rfl
  have hπ : ∀ σ, ((π σ : ↥(autOn L V)) : MulAut ↥V) = conjAct V (lift σ) := fun σ => rfl
  refine ⟨π, ?_, le_top, inf_le_right, fun _ _ _ => mem_top _, ?_, ?_, ?_, ?_⟩
  ·
    rintro ⟨a, g, hg, rfl⟩
    have hgL : (g : G) ∈ L := mem_subgroupOf.1 hg
    refine ⟨⟨S.frame.ρ g, (S.frame.image_L _).1 ⟨g, hgL, rfl⟩⟩, Subtype.ext ?_⟩
    show conjAct V (lift ⟨S.frame.ρ g, _⟩) = conjAct V g
    rw [s134_conjAct_eq_iff_rho S, hliftρ]
  ·
    rintro ⟨a, g, hg, rfl⟩ z hz
    have hgL : (g : G) ∈ L := mem_subgroupOf.1 hg
    rw [mem_subgroupOf] at hz ⊢
    have happ : ((conjAct V g z : ↥V) : G) = g * z * (g : G)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) z
    show ((conjAct V g z : ↥V) : G) ∈ centralizer (L : Set G)
    rw [happ, mem_centralizer_iff.mp hz (g : G) hgL, mul_inv_cancel_right]
    exact hz
  ·
    intro γ m hm
    exact G6.permAct_mem_coreMod _ hm
  ·
    intro γ m hm
    exact permAct_mem_ker γ.1 hm
  let ψ' : ↥V →* ↥(FFModel.altDn 6).sec := S.frame.ψ.toMonoidHom
  let β : ↥(⊤ : Subgroup ↥V) →* ↥(FFModel.altDn 6).sec ⧸
      (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec :=
    (QuotientGroup.mk' _).comp (ψ'.comp (⊤ : Subgroup ↥V).subtype)
  have hβ : ∀ u : ↥(⊤ : Subgroup ↥V), β u = (QuotientGroup.mk (ψ' u) :
      ↥(FFModel.altDn 6).sec ⧸ (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec) :=
    fun u => rfl
  refine ⟨β, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨v, hv⟩ := S.frame.ψ.surjective m
    exact ⟨⟨v, mem_top v⟩, by rw [hβ]; exact congrArg _ hv⟩
  · intro u
    have key : β u = 1 ↔ (S.frame.ψ u : P6) = 1 ∨ (S.frame.ψ u : P6) = G6.allOnes 6 := by
      rw [hβ, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact mem_ker_altDn_iff
    rw [key, mem_subgroupOf, S.mem_centralizer_L_iff]
    constructor
    · rintro (h | h)
      · left
        apply S.frame.ψ.injective
        rw [map_one]
        exact Subtype.ext h
      · right
        apply S.frame.ψ.injective
        rw [S.psi_zV]
        exact Subtype.ext h
    · rintro (h | h)
      · left
        rw [h, map_one]
        rfl
      · right
        rw [h, S.psi_zV]
  · intro γ u m hu hm hum
    have e1 : β ⟨_, hu⟩ = (QuotientGroup.mk (G6.coreAct 6 γ.1 (S.frame.ψ (u : ↥V))) :
        ↥(G6.coreMod 6) ⧸ (zpowers (G6.allOnes 6) ⊓ G6.coreMod 6).subgroupOf (G6.coreMod 6)) := by
      exact congrArg QuotientGroup.mk ((S.frame.equiv (lift γ) (u : ↥V)).trans
        (congrArg (fun σ => G6.coreAct 6 σ (S.frame.ψ (u : ↥V))) (hliftρ γ)))
    rw [e1]
    exact coreAct_mk_eq γ.1 (a := S.frame.ψ (u : ↥V)) (b := m) hum

theorem s134_not_L32 (S : A6.Setting134 G T L V) :
    ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := by
  intro hl
  obtain ⟨e6⟩ := s134_isA6On S
  have hdvd := card_autOn_dvd_quot S.frame.L_le (s134_pCoreOf_L_le S)
  rw [Nat.card_congr e6.toEquiv, A6.card_alt6] at hdvd
  obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel hl
  rw [Nat.card_congr e3.toEquiv, HSType.card_SL_three_two] at hdvd
  norm_num at hdvd

theorem s134_lemma13_2_2_seven (hC137 : C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (S : A6.Setting134 G T L V) :
    CharNormal (baum (r1Of T L V)) (L ⊔ T) ∨ H13.IsA6Block L := by
  by_cases hT6 : ∀ t : ↥(normalizer (V : Set G)), (t : G) ∈ T → Perm.sign (S.frame.ρ t) = 1
  ·
    left
    have hJ := s134_thompsonJ_r1Of_eq S hT6
    have hJB : thompsonJ (baum (r1Of T L V)) = thompsonJ (r1Of T L V) :=
      B6.thompsonJ_eq_of_le (B6.thompsonJ_le_baum _) inf_le_left
    refine ⟨thompsonJ (r1Of T L V), B6.thompsonJ_le_baum _, ?_, ?_, ?_⟩
    · intro h
      have hV := (s134_lemma13_2_2_six S).2.2
      rw [h] at hV
      exact S.irr.2.1 (le_bot_iff.1 hV)
    · rw [← hJB]
      exact S1414.characteristic_thompsonJ _
    · rw [hJ]
      exact (le_normalizer_pCoreOf 2 (L ⊔ T)).trans
        (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ _)
  obtain ⟨h5, -, -, -⟩ := h1332 G T L S.h13 L S.h13.faithful
  have htype := a6_or_hatA6_of_isA6On S.frame.L_le (s134_pCoreOf_L_le S) h5 (s134_isA6On S)
  have hcharL : CharTwo L := A5.charTwo_of_faithful S.h13.qtke.2.1 S.h13.sylow S.h13.faithful
  have hX := charTwo_sup_of_normalizes S.h13.sylow.1 S.T_le_NL hcharL
  have hsyl := A5.isSylowTwoOf_of_le S.h13.sylow (le_sup_right : T ≤ L ⊔ T)
  have hLT : ∀ x ∈ L ⊔ T, ∃ l ∈ L, ∃ t ∈ T, x = l * t := fun x hx => s134_mul_decomp S hx
  have hVL : ⁅V, L⁆ ≠ ⊥ := by rw [S.irr.2.2.2.1]; exact S.irr.2.1
  have hdyn := s134_alternatingNatural S
  have hM := s134_L1T_eq_NLTV1 S
  have hZ8 : ∀ l : Subgroup G, Nat.card ↥l = 4 * Nat.card ↥(V ⊓ centralizer (L : Set G)) →
      Nat.card ↥l = 8 := fun l h => by rw [h, S.card_ZV]
  rcases htype with he | hhat
  · have P := s134Plus_L1 S he
    rcases hC137 G (L ⊔ T) T V L (L₁Of L (fsuV1 T V) ⊔ T)
        ((L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G)) hX hsyl hLT S.h13.faithful.1.2.1 hcharL
        (Or.inr (Or.inl he)) (Or.inr (Or.inr hdyn)) le_sup_right hM.le
        (s134_NLTV1_lt S) (s134_NLTV1_max S) (Or.inl hM) (s134_reduced S) hVL
        (fun h => absurd h (s134_not_L32 S)) with h | h | ⟨h4, -⟩ | ⟨-, ⟨l, hZl, hlV, hl4, hlN⟩, -⟩
    · left
      rwa [P.pCoreOf_eq_r1Of] at h
    · exact Or.inr (h.2.1 he)
    · exact absurd h4 (s134_card_autOn_ne S)
    · exact (P.no_line hZl hlV (hZ8 l hl4) (le_sup_left.trans hlN)).elim
  · have P := s134Plus_l1plus S hhat
    have hPM : l1plus T L V ⊔ T ≤ (L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G) :=
      (sup_le_sup_right P.le_L1 T).trans hM.le
    rcases hC137 G (L ⊔ T) T V L (l1plus T L V ⊔ T)
        ((L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G)) hX hsyl hLT S.h13.faithful.1.2.1 hcharL
        (Or.inr (Or.inr (Or.inl hhat))) (Or.inr (Or.inr hdyn)) le_sup_right hPM
        (s134_NLTV1_lt S) (s134_NLTV1_max S)
        (Or.inr ⟨hhat, hM ▸ P.hat_index hhat, P.not_oTwoUpper_le_o2Z⟩) (s134_reduced S) hVL
        (fun h => absurd h (s134_not_L32 S)) with h | h | ⟨h4, -⟩ | ⟨-, ⟨l, hZl, hlV, hl4, hlN⟩, -⟩
    · left
      rwa [P.pCoreOf_eq_r1Of] at h
    · exact absurd (h.2.2.1 hhat) (s134_not_isHatBlock S hhat)
    · exact absurd h4 (s134_card_autOn_ne S)
    · exact (P.no_line hZl hlV (hZ8 l hl4) (le_sup_left.trans hlN)).elim

end CFSG.Quasithin.H13.U3
