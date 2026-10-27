module

public import CFSG.Quasithin.Vol2.Ch4Sec3SL3
public import CFSG.Quasithin.Vol2.Ch4Sec3Sp4Mat
public import CFSG.Quasithin.Vol2.Ch4Sec3Sp4Z

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped commutatorElement Pointwise

theorem card_statedSp_two_of_card_four {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) : Nat.card ↥(StatedSp 2 F) = 979200 := by
  rw [SymplecticFlag.card_statedSp, Nat.card_eq_fintype_card, hF,
    show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  norm_num

theorem sl3_card_ne_sp4 {m : ℕ} :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ 979200 := by
  intro h
  by_cases hm : m < 4
  · interval_cases m <;> simp at h
  · have h16 : 16 ≤ 2 ^ m :=
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 4096 ≤ (2 ^ m) ^ 3 :=
      calc (4096 : ℕ) = 16 ^ 3 := by norm_num
        _ ≤ (2 ^ m) ^ 3 := Nat.pow_le_pow_left h16 3
    have h2 : 255 ≤ (2 ^ m) ^ 2 - 1 := by
      have : 256 ≤ (2 ^ m) ^ 2 :=
        calc (256 : ℕ) = 16 ^ 2 := by norm_num
          _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h16 2
      omega
    have h3 : 4095 ≤ (2 ^ m) ^ 3 - 1 := by omega
    have : 4096 * (255 * 4095) ≤ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    omega

variable {G : Type} [Group G] [Finite G]

namespace Setting432K

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (sk : Setting432K G T M L n I H K t)
include sk

theorem not_isSp4Block (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hZ : Gap437Sp4Z) (hchar : CharTwo K)
    (h41 : C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
      ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K) :
    ¬ IsSp4Block K := by
  classical
  intro hblk
  have hblk₀ := hblk
  set V := ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ with hV
  set S := T ⊓ H with hS
  set φt := (MulAut.conj t).toMonoidHom with hφt
  obtain ⟨hshort, F₀, _, _, hF₀, α₀, hα₀, hker₀, -⟩ := hblk
  have hSK := sk.S_le_normalizer
  have hLK := sk.L_le_K
  have hcardK : Nat.card (ModO2 K) = 979200 := by
    rw [card_modO2_of_surjective α₀ hα₀ hker₀, card_statedSp_two_of_card_four hF₀]
  have hc2 : C41Case2 H (pCoreOf 2 I) (H ⊓ M) L V K := by
    rcases h41.2.2.2 with c1 | c2 | c3 | c4
    · exfalso
      obtain ⟨m, hm, -, -, ⟨-, α₁, hα₁, hker₁, -⟩, -, -⟩ := c1
      have h1 := card_modO2_of_surjective α₁ hα₁ hker₁
      rw [card_of_alt' (by omega) (MulEquiv.refl _), hcardK] at h1
      rcases hm with rfl | rfl <;> simp [Nat.factorial] at h1
    · exact c2
    · exfalso
      obtain ⟨n', F', _, _, -, hF', ⟨e⟩, -⟩ := c3
      have h1 : Nat.card (ModO2 K) = Nat.card ↥(StatedSL 3 F') := Nat.card_congr e.toEquiv
      rw [hcardK, card_statedSL_three, hF'] at h1
      exact sl3_card_ne_sp4 h1.symm
    · exfalso
      obtain ⟨h4, -, -⟩ := c4
      rcases h4 with h | h
      · have h1 := F420.card_of_l42 h
        rw [hcardK] at h1
        norm_num at h1
      · have h1 := F420.card_of_l52 h
        rw [hcardK] at h1
        norm_num at h1
  have hZK : blockZ K = ⊥ := hZ G T M L n I H K t sk hchar hblk₀ hc2
  obtain ⟨-, F, _, _, α, β, hF, ⟨hα, hkerα, hβ, hkerβ, hequiv⟩, hFL, hpar, hMK, hLpsl⟩ := hc2
  rw [hZK, sup_bot_eq] at hFL
  obtain ⟨hVU, W, hW, hWiff⟩ := hFL
  have hLeq : conjClosure L (H ⊓ M) = L := h41.1.symm
  have h60 : Nat.card (ModO2 L) = 60 := by
    have e := congrArg (fun X : Subgroup G => Nat.card (ModO2 X)) hLeq
    rw [← e, F420.card_of_statedPSL_two_two hLpsl]
    norm_num
  set Q := pCoreOf 2 K with hQ
  obtain ⟨Ut, hUt⟩ : ∃ Ut : Subgroup G, Ut = (blockU K).map (MulAut.conj t).toMonoidHom := ⟨_, rfl⟩
  have hUQ : (blockU K) ≤ Q := commutator_le_left_of_le_normalizer (le_normalizer_pCoreOf 2 K)
  have hQK : Q ≤ K := pCoreOf_le 2 K
  have hQS : Q ≤ S := sk.pCoreOf_K_le_S hR hC h37 h38 h39
  have hUS : (blockU K) ≤ S := hUQ.trans hQS
  have hKU : K ≤ Subgroup.normalizer ((blockU K) : Set G) :=
    Subgroup.normalizer_commutator_ge_right Q K
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 K
  have hSU : S ≤ Subgroup.normalizer ((blockU K) : Set G) := fun s hs =>
    mem_normalizer_commutator ((normalizer_le_normalizer_pCoreOf 2 K) (hSK hs)) (hSK hs)
  have htS : S.map (MulAut.conj t).toMonoidHom = S :=
    map_conj_eq_of_mem_normalizer sk.t_normalizer
  have hUtS : Ut ≤ S := hUt ▸ htS ▸ map_conj_mono hUS t
  have hSUt : S ≤ Subgroup.normalizer (Ut : Set G) := by
    intro s hs
    apply mem_normalizer_of_map_conj_le
    have hs' : t⁻¹ * s * t ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ sk.t_normalizer) s).mp hs
      rwa [inv_inv] at this
    have e : s * t = t * (t⁻¹ * s * t) := by group
    rw [hUt, ← map_conj_mul, e, map_conj_mul, map_conj_eq_of_mem_normalizer (hSU hs')]
  have hUab : ∀ u ∈ (blockU K), ∀ u' ∈ (blockU K), u * u' = u' * u := fun u hu u' hu' =>
    (Subgroup.mem_centralizer_iff.mp (hshort.2.2.1.1 hu).2 u' (hUQ hu')).symm
  have hUtab : ∀ x ∈ Ut, ∀ y ∈ Ut, x * y = y * x := by
    rw [hUt]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hUab x hx y hy]
  have htL : t ∈ Subgroup.normalizer (L : Set G) :=
    sk.base.hyp.normal (sk.base.hyp.T_le sk.t_mem)
  have htV : t ∈ Subgroup.normalizer (V : Set G) :=
    mem_normalizer_commutator
      (normalizer_le_normalizer_omegaOneCenterOf _ (sk.base.le_normalizer_Rp sk.t_mem)) htL
  have hLt : L.map (MulAut.conj t).toMonoidHom = L := map_conj_eq_of_mem_normalizer htL
  have hVt : V.map (MulAut.conj t).toMonoidHom = V := map_conj_eq_of_mem_normalizer htV
  have hVUt : V ≤ Ut := hUt ▸ hVt ▸ map_conj_mono hVU t
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := Subgroup.normalizer_commutator_ge_right _ L
  have hLU : L ≤ Subgroup.normalizer ((blockU K) : Set G) := hLK.trans hKU
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := hLK.trans hKQ
  have hLUt : L ≤ Subgroup.normalizer (Ut : Set G) := by
    intro l hl
    apply mem_normalizer_of_map_conj_le
    have hl' : t⁻¹ * l * t ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htL) l).mp hl
      rwa [inv_inv] at this
    have e : l * t = t * (t⁻¹ * l * t) := by group
    rw [hUt, ← map_conj_mul, e, map_conj_mul, map_conj_eq_of_mem_normalizer (hLU hl')]
  set αG : K →* GL (Fin 2 ⊕ Fin 2) F := (StatedSp 2 F).subtype.comp α with hαG
  have hstabW : ∀ k : K, (k : G) ∈ Subgroup.normalizer (V : Set G) → ∀ w ∈ W,
      (αG k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W := by
    intro k hk w hw
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd w)
    have huV : (u : G) ∈ V := (hWiff u).mpr (by rw [hu, toAdd_ofAdd]; exact hw)
    let v : (blockU K) := ⟨k * u * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU k.2) u).mp u.2⟩
    have h1 := hequiv k u v rfl
    rw [hu, toAdd_ofAdd] at h1
    change (((α k : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W
    rw [← h1]
    exact (hWiff v).mp ((Subgroup.mem_normalizer_iff.mp hk u).mp huV)
  obtain ⟨⟨-, SK, hSKsyl, hSKN⟩, -, -⟩ := hpar
  have hSKV : SK ≤ Subgroup.normalizer (V : Set G) := by
    intro s hs
    have h1 : s ∈ K ⊓ Subgroup.normalizer (SK : Set G) :=
      ⟨hSKsyl.1 hs, Subgroup.le_normalizer hs⟩
    have h2 := hSKN h1
    rw [hMK] at h2
    exact h2.2
  have hiso : SymplecticFlag.IsTotallyIsotropic (pairedSympForm F 2) W := by
    refine Sp4.isTotallyIsotropic_of_isPGroup hF ((SK.subgroupOf K).map α)
      ((hSKsyl.2.1.comap_of_injective K.subtype K.subtype_injective).map α) ?_ hW ?_
    · intro h2
      exact hSKsyl.2.2 (h2.trans (Subgroup.index_map_dvd _ hα))
    · rintro _ ⟨k, hk, rfl⟩ w hw
      exact hstabW k (hSKV hk) w hw
  set f : L →* GL (Fin 2 ⊕ Fin 2) F := αG.comp (Subgroup.inclusion hLK) with hf
  have hLperf : commutator L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subtype_commutator, sk.base.hyp.commutator_eq, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hd : Sp4.LeviData F W f :=
    { card := hF
      finrank := hW
      iso := hiso
      mem := fun l => (α _).2
      stab := fun l w hw => hstabW _ (hLV l.2) w hw
      perf := hLperf
      ker := by
        rintro ⟨l, hl⟩
        have h1 : Subgroup.inclusion hLK l ∈ α.ker :=
          MonoidHom.mem_ker.mpr (Subtype.ext (MonoidHom.mem_ker.mp hl))
        rw [hkerα] at h1
        have h2 : ((l : L) : G) ∈ Q := (mem_pCoreOf_iff' _).mpr h1
        obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 K) ⟨l, h2⟩
        refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
        have := congrArg Subtype.val hk
        simpa using this
      card60 := h60 }
  have hT1 := hd.exists_mulVec_sub_mem
  have hIrr : ∀ U₁ : Subgroup G, V ≤ U₁ → U₁ ≤ (blockU K) → L ≤ Subgroup.normalizer (U₁ : Set G) →
      ¬ U₁ ≤ V → U₁ = (blockU K) := by
    intro U₁ hVU₁ hU₁U hLU₁ hnot
    obtain ⟨u₁, hu₁, hu₁V⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    refine le_antisymm hU₁U fun u hu => ?_
    by_cases huV : u ∈ V
    · exact hVU₁ huV
    · let a : (blockU K) := ⟨u₁, hU₁U hu₁⟩
      let b : (blockU K) := ⟨u, hu⟩
      have ha : Multiplicative.toAdd (β a) ∉ W := fun h => hu₁V ((hWiff a).mpr h)
      have hb : Multiplicative.toAdd (β b) ∉ W := fun h => huV ((hWiff b).mpr h)
      obtain ⟨l, hl⟩ := hT1 _ _ ha hb
      let c : (blockU K) := ⟨l * u₁ * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hLU l.2) u₁).mp
        (hU₁U hu₁)⟩
      have h1 := hequiv (Subgroup.inclusion hLK l) a c rfl
      have h2 : ((c * b⁻¹ : (blockU K)) : G) ∈ V := by
        apply (hWiff _).mpr
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv, h1, ← sub_eq_add_neg]
        exact hl
      have h3 : (c : G) ∈ U₁ := (Subgroup.mem_normalizer_iff.mp (hLU₁ l.2) u₁).mp hu₁
      have e : u = ((c * b⁻¹ : (blockU K)) : G)⁻¹ * c := by
        show (b : G) = ((c * b⁻¹ : (blockU K)) : G)⁻¹ * c
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact U₁.mul_mem (U₁.inv_mem (hVU₁ h2)) h3
  obtain ⟨c₀, hc0, hc1⟩ : ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset F) ⊆ ({0, 1} : Finset F) := fun l _ => by
      by_cases hl : l = 0
      · simp [hl]
      · simp [h l hl]
    have h5 := Finset.card_le_card hsub
    rw [Finset.card_univ, hF] at h5
    have h6 := Finset.card_insert_le (0 : F) ({1} : Finset F)
    rw [Finset.card_singleton] at h6
    omega
  have hfixU : ∀ u ∈ (blockU K), (∀ l ∈ L, ⁅u, l⁆ ∈ V) → u ∈ V := by
    intro u hu hcomm
    by_contra huV
    let a : (blockU K) := ⟨u, hu⟩
    have ha : Multiplicative.toAdd (β a) ∉ W := fun h => huV ((hWiff a).mpr h)
    have hca : c₀ • Multiplicative.toAdd (β a) ∉ W := fun h => ha (by
      have := W.smul_mem c₀⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this)
    obtain ⟨l, hl⟩ := hT1 _ _ ha hca
    let c : (blockU K) := ⟨l * u * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hLU l.2) u).mp hu⟩
    have h1 : Multiplicative.toAdd (β c) =
        (f l : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ Multiplicative.toAdd (β a) :=
      hequiv (Subgroup.inclusion hLK l) a c rfl
    have h2 : ((c * a⁻¹ : (blockU K)) : G) ∈ V := by
      have e : ((c * a⁻¹ : (blockU K)) : G) = ⁅u, (l : G)⁆⁻¹ := by
        show (l : G) * u * (l : G)⁻¹ * u⁻¹ = ⁅u, (l : G)⁆⁻¹
        rw [commutatorElement_def]
        group
      rw [e]
      exact V.inv_mem (hcomm l l.2)
    have h3 := (hWiff _).mp h2
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, h1] at h3
    have h4 : (c₀ - 1) • Multiplicative.toAdd (β a) ∈ W := by
      have := W.sub_mem h3 hl
      convert this using 1
      rw [sub_smul, one_smul]
      abel
    apply ha
    have := W.smul_mem (c₀ - 1)⁻¹ h4
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hc1), one_smul] at this
  have hfixUt : ∀ x ∈ Ut, (∀ l ∈ L, ⁅x, l⁆ ∈ V) → x ∈ V := by
    rw [hUt]
    rintro _ ⟨u, hu, rfl⟩ hcomm
    have hu' : u ∈ V := by
      refine hfixU u hu fun l hl => ?_
      have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htL l).mp hl
      have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htV) _).mp (hcomm _ hl')
      have e : t⁻¹ * ⁅(MulAut.conj t).toMonoidHom u, t * l * t⁻¹⁆ * t⁻¹⁻¹ = ⁅u, l⁆ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rwa [e] at h2
    have := (Subgroup.mem_normalizer_iff.mp htV u).mp hu'
    simpa [MulAut.conj_apply] using this
  have hUtQ : ¬ Ut ≤ Q := fun h => sk.not_commutator_conj_blockU_le hR hC h37 h38 h39 hchar
    (hUt ▸ (Subgroup.commutator_mono h le_rfl).trans (commutator_le_left_of_le_normalizer hKQ))
  have hcardUt : Nat.card Ut = Nat.card (blockU K) := by
    rw [hUt]
    exact (Nat.card_congr ((blockU K).equivMapOfInjective _ (MulAut.conj t).injective).toEquiv).symm
  have hG1 : (blockU K) ⊓ Ut = V := by
    by_contra hne
    have h1 := hIrr ((blockU K) ⊓ Ut) (le_inf hVU hVUt) inf_le_left
      (fun l hl => mem_normalizer_inf (hLU hl) (hLUt hl))
      (fun h => hne (le_antisymm h (le_inf hVU hVUt)))
    have h2 : (blockU K) ≤ Ut := by
      rw [← h1]
      exact inf_le_right
    have h3 : (blockU K) = Ut := Subgroup.eq_of_le_of_card_ge h2 hcardUt.le
    exact hUtQ (h3 ▸ hUQ)
  have hG2 : Ut ⊓ Q ≤ V := by
    set U₁ := (blockU K) ⊓ Q.comap (MulAut.conj t).toMonoidHom with hU₁
    have hVU₁ : V ≤ U₁ := fun v hv =>
      ⟨hVU hv, hUQ (hVU ((Subgroup.mem_normalizer_iff.mp htV v).mp hv))⟩
    have hLU₁ : L ≤ Subgroup.normalizer (U₁ : Set G) := by
      intro l hl
      apply mem_normalizer_of_map_conj_le
      rintro _ ⟨u, ⟨huU, huQ⟩, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hLU hl) u).mp huU, ?_⟩
      have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htL l).mp hl
      have h1 := (Subgroup.mem_normalizer_iff.mp (hLQ hl') _).mp huQ
      have e : (MulAut.conj t).toMonoidHom ((MulAut.conj l).toMonoidHom u) =
          t * l * t⁻¹ * (MulAut.conj t).toMonoidHom u * (t * l * t⁻¹)⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      show (MulAut.conj t).toMonoidHom ((MulAut.conj l).toMonoidHom u) ∈ Q
      rw [e]
      exact h1
    have hU₁V : U₁ ≤ V := by
      by_contra hnot
      have h1 := hIrr U₁ hVU₁ inf_le_left hLU₁ hnot
      apply hUtQ
      rw [hUt]
      rintro _ ⟨u, hu, rfl⟩
      have : u ∈ U₁ := h1 ▸ hu
      exact this.2
    rw [hUt]
    rintro x ⟨⟨u, hu, rfl⟩, hxQ⟩
    have := hU₁V ⟨hu, hxQ⟩
    have := (Subgroup.mem_normalizer_iff.mp htV u).mp this
    simpa [MulAut.conj_apply] using this
  have hULV : ⁅(blockU K), L⁆ ⊔ V = (blockU K) := by
    by_contra hne
    have hle : ⁅(blockU K), L⁆ ⊔ V ≤ (blockU K) :=
      _root_.sup_le (commutator_le_left_of_le_normalizer hLU) hVU
    have hLN : L ≤ Subgroup.normalizer ((⁅(blockU K), L⁆ ⊔ V : Subgroup G) : Set G) := by
      intro l hl
      apply mem_normalizer_of_map_conj_le
      rw [Subgroup.map_sup,
        map_conj_eq_of_mem_normalizer (Subgroup.normalizer_commutator_ge_right (blockU K) L hl),
        map_conj_eq_of_mem_normalizer (hLV hl)]
    have h1 : ⁅(blockU K), L⁆ ⊔ V ≤ V := by
      by_contra hnot
      exact hne (hIrr _ le_sup_right hle hLN hnot)
    have hUV : (blockU K) ≤ V := fun u hu => hfixU u hu fun l hl =>
      h1 (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu hl))
    have hWtop : W = ⊤ := by
      rw [eq_top_iff]
      intro w _
      obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd w)
      have := (hWiff u).mp (hUV u.2)
      rwa [hu, toAdd_ofAdd] at this
    rw [hWtop, finrank_top, Module.finrank_fintype_fun_eq_card] at hW
    simp at hW
  have hUtK : Ut ≤ K := by
    have h1 : Ut = ⁅Ut, L⁆ ⊔ V := by
      rw [hUt]
      conv_lhs => rw [← hULV]
      rw [Subgroup.map_sup, Subgroup.map_commutator, hLt, hVt]
    rw [h1]
    exact _root_.sup_le ((commutator_le_right_of_le_normalizer
      (hUtS.trans (inf_le_left.trans (sk.base.hyp.T_le.trans sk.base.hyp.normal)))).trans hLK)
      (hVU.trans (hUQ.trans hQK))
  set X : Subgroup (GL (Fin 2 ⊕ Fin 2) F) := (Ut.subgroupOf K).map αG with hX
  have hXmem : ∀ x ∈ X, ∃ k : K, (k : G) ∈ Ut ∧ αG k = x := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  have hmemX : ∀ k : K, (k : G) ∈ Ut → αG k ∈ X := fun k hk => ⟨k, hk, rfl⟩
  have hXS : X ≤ StatedSp 2 F := by
    rintro _ ⟨k, -, rfl⟩
    exact (α k).2
  have hX1 : ∀ x ∈ X, ∀ w ∈ W, (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w = w := by
    intro x hx w hw
    obtain ⟨k, hk, rfl⟩ := hXmem x hx
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd w)
    have huV : (u : G) ∈ V := (hWiff u).mpr (by rw [hu, toAdd_ofAdd]; exact hw)
    have hcomm : (u : G) = k * u * (k : G)⁻¹ := by
      rw [hUtab _ hk _ (hVUt huV), mul_inv_cancel_right]
    have h1 : Multiplicative.toAdd (β u) =
        (αG k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ Multiplicative.toAdd (β u) :=
      hequiv k u u hcomm
    rw [hu, toAdd_ofAdd] at h1
    exact h1.symm
  have hUtU : ⁅Ut, blockU K⁆ ≤ V := by
    rw [← hG1]
    exact le_inf (commutator_le_right_of_le_normalizer (hUtS.trans hSU))
      (commutator_le_left_of_le_normalizer (hUS.trans hSUt))
  have hX2 : ∀ x ∈ X, ∀ v, (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v - v ∈ W := by
    intro x hx v
    obtain ⟨k, hk, rfl⟩ := hXmem x hx
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd v)
    let c : blockU K := ⟨k * u * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU k.2) u).mp u.2⟩
    have h1 : Multiplicative.toAdd (β c) =
        (αG k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ Multiplicative.toAdd (β u) :=
      hequiv k u c rfl
    rw [hu, toAdd_ofAdd] at h1
    have h2 : ((c * u⁻¹ : blockU K) : G) ∈ V := by
      have e : ((c * u⁻¹ : blockU K) : G) = ⁅(k : G), (u : G)⁆ := by
        show (k : G) * u * (k : G)⁻¹ * (u : G)⁻¹ = ⁅(k : G), (u : G)⁆
        rw [commutatorElement_def]
      rw [e]
      exact hUtU (Subgroup.commutator_mem_commutator hk u.2)
    have h3 := (hWiff _).mp h2
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, h1, hu, toAdd_ofAdd, ← sub_eq_add_neg] at h3
    exact h3
  have hXN : ∀ l : L, f l ∈ Subgroup.normalizer (X : Set (GL (Fin 2 ⊕ Fin 2) F)) := by
    intro l
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hXmem x hx
    have hk' : ((Subgroup.inclusion hLK l * k * (Subgroup.inclusion hLK l)⁻¹ : K) : G) ∈ Ut :=
      (Subgroup.mem_normalizer_iff.mp (hLUt l.2) k).mp hk
    have h1 := hmemX _ hk'
    rw [map_mul, map_mul, map_inv] at h1
    exact h1
  have hXne : X ≠ ⊥ := by
    intro hbot
    apply hUtQ
    intro x hx
    have hxK := hUtK hx
    have h1 := hmemX ⟨x, hxK⟩ hx
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hxK⟩ : K) ∈ α.ker := MonoidHom.mem_ker.mpr (Subtype.ext h1)
    rw [hkerα] at h2
    exact (mem_pCoreOf_iff' _).mpr h2
  have hXC : ∀ x ∈ X, (∀ l : L, f l * x = x * f l) → x = 1 := by
    intro x hx hc
    obtain ⟨k, hk, rfl⟩ := hXmem x hx
    have hkV : (k : G) ∈ V := by
      refine hfixUt _ hk fun l hl => ?_
      set il := Subgroup.inclusion hLK ⟨l, hl⟩ with hil
      have h1 : αG il * αG k = αG k * αG il := hc ⟨l, hl⟩
      have h2 : k * il * k⁻¹ * il⁻¹ ∈ α.ker := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change αG (k * il * k⁻¹ * il⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        calc αG k * αG il * (αG k)⁻¹ * (αG il)⁻¹ =
            (αG k * αG il) * (αG il * αG k)⁻¹ := by group
          _ = 1 := by rw [h1, mul_inv_cancel]
      rw [hkerα] at h2
      have h4 : ⁅(k : G), l⁆ ∈ Q := by
        have := (mem_pCoreOf_iff' _).mpr h2
        simpa [commutatorElement_def, hil] using this
      have h5 : ⁅(k : G), l⁆ ∈ Ut := by
        have h6 : l * (k : G)⁻¹ * l⁻¹ ∈ Ut :=
          (Subgroup.mem_normalizer_iff.mp (hLUt hl) _).mp (Ut.inv_mem hk)
        have e : ⁅(k : G), l⁆ = k * (l * (k : G)⁻¹ * l⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact Ut.mul_mem hk h6
      exact hG2 ⟨h5, h4⟩
    have hkQ : (k : G) ∈ Q := hUQ (hVU hkV)
    have h1 : k ∈ α.ker := by
      rw [hkerα]
      exact (mem_pCoreOf_iff' k).mp hkQ
    change ((α k : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) = 1
    rw [MonoidHom.mem_ker.mp h1]
    rfl
  exact hd.false_of_radical X hXS hX1 hX2 hXN hXne hXC

end Setting432K

theorem lemma437Sp4_holds (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hZ : Gap437Sp4Z) : Lemma437Sp4 :=
  fun _ _ _ _ _ _ _ _ _ _ _ sk hchar h41 =>
    sk.not_isSp4Block hR hC h37 h38 h39 hZ hchar h41

end CFSG.Quasithin.H13.Ch4
