module

public import CFSG.Quasithin.Vol2.Ch4Sec3Sp4Fix
public import CFSG.Quasithin.Vol2.Ch4Sec3Sp4Z
public import CFSG.Quasithin.Vol2.Ch4Sec3Sp4ZK

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Setting432K

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (sk : Setting432K G T M L n I H K t)
include sk

theorem false_of_sp4Case2 (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hchar : CharTwo K)
    (hc2 : C41Case2 H (pCoreOf 2 I) (H ⊓ M) L
      ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K) : False := by
  classical
  set V := ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ with hV
  set S := T ⊓ H with hS
  have hSK := sk.S_le_normalizer
  have hLK := sk.L_le_K
  obtain ⟨⟨hshort, -⟩, F, _, _, α, β, hF, hmat, hFL, hpar, hMK, hLpsl⟩ := hc2
  obtain ⟨hα, hkerα, hβ, hkerβ, hequiv⟩ := id hmat
  set V₁ := V ⊔ blockZ K with hV₁
  obtain ⟨hV₁U, W, hW, hWiff⟩ := hFL
  have hVU : V ≤ blockU K := le_sup_left.trans hV₁U
  have hLeq : conjClosure L (H ⊓ M) = L :=
    le_antisymm (conjClosure_le fun _ hs x hx =>
      (Subgroup.mem_normalizer_iff.mp ((inf_le_right.trans sk.base.hyp.normal) hs) x).mp hx)
      (le_conjClosure L _)
  have h60 : Nat.card (ModO2 L) = 60 := by
    have e := congrArg (fun X : Subgroup G => Nat.card (ModO2 X)) hLeq
    rw [← e, F420.card_of_statedPSL_two_two hLpsl]
    norm_num
  set Q := pCoreOf 2 K with hQ
  obtain ⟨Ut, hUt⟩ : ∃ Ut : Subgroup G, Ut = (blockU K).map (MulAut.conj t).toMonoidHom :=
    ⟨_, rfl⟩
  obtain ⟨Zt, hZt⟩ : ∃ Zt : Subgroup G, Zt = (blockZ K).map (MulAut.conj t).toMonoidHom :=
    ⟨_, rfl⟩
  obtain ⟨V₁t, hV₁t⟩ : ∃ X : Subgroup G, X = V₁.map (MulAut.conj t).toMonoidHom := ⟨_, rfl⟩
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
    rw [hUt]
    exact Sp4Z.le_normalizer_map_conj sk.t_normalizer hSU
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
  have hZU : blockZ K ≤ blockU K := inf_le_left
  have hZC : blockZ K ≤ Subgroup.centralizer (K : Set G) := inf_le_right
  have hKZ : K ≤ Subgroup.centralizer (blockZ K : Set G) := fun k hk =>
    Subgroup.mem_centralizer_iff.mpr fun _ hz =>
      (Subgroup.mem_centralizer_iff.mp (hZC hz) k hk).symm
  have hZtU : Zt ≤ Ut := by
    rw [hZt, hUt]
    exact map_conj_mono hZU t
  have hSZ : S ≤ Subgroup.normalizer (blockZ K : Set G) := fun s hs =>
    Sp4Z.mem_normalizer_blockZ (hSK hs)
  have hSZt : S ≤ Subgroup.normalizer (Zt : Set G) := by
    rw [hZt]
    exact Sp4Z.le_normalizer_map_conj sk.t_normalizer hSZ
  have hLZ : L ≤ Subgroup.centralizer (blockZ K : Set G) := sk.le_centralizer_blockZ
  have hLZt : L ≤ Subgroup.centralizer (Zt : Set G) := by
    rw [hZt]
    exact sk.le_centralizer_map_conj_blockZ
  have hZZt : blockZ K ⊓ Zt = ⊥ := by
    rw [hZt]
    exact sk.blockZ_inf_map_conj_eq_bot
  have hV₁t' : V₁t = V ⊔ Zt := by rw [hV₁t, hV₁, Subgroup.map_sup, hVt, hZt]
  have hKV₁ : ∀ k ∈ K, k ∈ Subgroup.normalizer (V : Set G) →
      k ∈ Subgroup.normalizer (V₁ : Set G) := by
    intro k hk hkV
    apply mem_normalizer_of_map_conj_le
    rw [hV₁, Subgroup.map_sup, map_conj_eq_of_mem_normalizer hkV,
      map_conj_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ (hKZ hk))]
  have hLV₁ : ∀ l ∈ L, l ∈ Subgroup.normalizer (V₁ : Set G) := fun l hl =>
    hKV₁ l (hLK hl) (hLV hl)
  set αG : K →* GL (Fin 2 ⊕ Fin 2) F := (StatedSp 2 F).subtype.comp α with hαG
  have hstabW : ∀ k : K, (k : G) ∈ Subgroup.normalizer (V₁ : Set G) → ∀ w ∈ W,
      (αG k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W := by
    intro k hk w hw
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd w)
    have huV : (u : G) ∈ V₁ := (hWiff u).mpr (by rw [hu, toAdd_ofAdd]; exact hw)
    let v : (blockU K) := ⟨k * u * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU k.2) u).mp u.2⟩
    have h1 := hequiv k u v rfl
    rw [hu, toAdd_ofAdd] at h1
    change (((α k : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W
    rw [← h1]
    exact (hWiff v).mp ((Subgroup.mem_normalizer_iff.mp hk u).mp huV)
  obtain ⟨⟨-, SK, hSKsyl, hSKN⟩, -, -⟩ := hpar
  have hSKV : SK ≤ Subgroup.normalizer (V₁ : Set G) := by
    intro s hs
    have h1 : s ∈ K ⊓ Subgroup.normalizer (SK : Set G) :=
      ⟨hSKsyl.1 hs, Subgroup.le_normalizer hs⟩
    have h2 := hSKN h1
    rw [hMK] at h2
    exact hKV₁ s (hSKsyl.1 hs) h2.2
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
      stab := fun l w hw => hstabW _ (hLV₁ _ l.2) w hw
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
  have hIrr : ∀ U₁ : Subgroup G, V₁ ≤ U₁ → U₁ ≤ (blockU K) →
      L ≤ Subgroup.normalizer (U₁ : Set G) → ¬ U₁ ≤ V₁ → U₁ = (blockU K) := by
    intro U₁ hVU₁ hU₁U hLU₁ hnot
    obtain ⟨u₁, hu₁, hu₁V⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    refine le_antisymm hU₁U fun u hu => ?_
    by_cases huV : u ∈ V₁
    · exact hVU₁ huV
    · let a : (blockU K) := ⟨u₁, hU₁U hu₁⟩
      let b : (blockU K) := ⟨u, hu⟩
      have ha : Multiplicative.toAdd (β a) ∉ W := fun h => hu₁V ((hWiff a).mpr h)
      have hb : Multiplicative.toAdd (β b) ∉ W := fun h => huV ((hWiff b).mpr h)
      obtain ⟨l, hl⟩ := hT1 _ _ ha hb
      let c : (blockU K) := ⟨l * u₁ * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hLU l.2) u₁).mp
        (hU₁U hu₁)⟩
      have h1 := hequiv (Subgroup.inclusion hLK l) a c rfl
      have h2 : ((c * b⁻¹ : (blockU K)) : G) ∈ V₁ := by
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
  obtain ⟨c₀, hc0, hc1⟩ := Sp4.exists_ne_zero_ne_one hF
  have hfixU : ∀ u ∈ (blockU K), (∀ l ∈ L, ⁅u, l⁆ ∈ V₁) → u ∈ V₁ := by
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
    have h2 : ((c * a⁻¹ : (blockU K)) : G) ∈ V₁ := by
      have e : ((c * a⁻¹ : (blockU K)) : G) = ⁅u, (l : G)⁆⁻¹ := by
        show (l : G) * u * (l : G)⁻¹ * u⁻¹ = ⁅u, (l : G)⁆⁻¹
        rw [commutatorElement_def]
        group
      rw [e]
      exact V₁.inv_mem (hcomm l l.2)
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
  have hfixUt : ∀ x ∈ Ut, (∀ l ∈ L, ⁅x, l⁆ ∈ V₁t) → x ∈ V₁t := by
    rw [hUt, hV₁t]
    rintro _ ⟨u, hu, rfl⟩ hcomm
    have hu' : u ∈ V₁ := by
      refine hfixU u hu fun l hl => ?_
      have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htL l).mp hl
      have h1 := Subgroup.mem_map_equiv.mp (hcomm _ hl')
      have e : (MulAut.conj t).symm ⁅(MulAut.conj t).toMonoidHom u, t * l * t⁻¹⁆ = ⁅u, l⁆ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_symm_apply,
          commutatorElement_def]
        group
      rwa [e] at h1
    exact ⟨u, hu', rfl⟩
  have hCLU : ∀ u ∈ blockU K, (∀ l ∈ L, l * u = u * l) → u ∈ blockZ K := by
    intro u hu hcomm
    have hfix : ∀ l : L, (f l : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        Multiplicative.toAdd (β ⟨u, hu⟩) = Multiplicative.toAdd (β ⟨u, hu⟩) := by
      intro l
      have h1 := hequiv (Subgroup.inclusion hLK l) ⟨u, hu⟩ ⟨u, hu⟩ (by
        show u = l * u * (l : G)⁻¹
        rw [hcomm l l.2, mul_inv_cancel_right])
      exact h1.symm
    have h0 := hd.eq_zero_of_forall_mulVec_eq hfix
    have h1 : (⟨u, hu⟩ : blockU K) ∈ β.ker := by
      rw [MonoidHom.mem_ker, ← ofAdd_toAdd (β ⟨u, hu⟩), h0, ofAdd_zero]
    rw [hkerβ] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hCLUt : ∀ x ∈ Ut, (∀ l ∈ L, l * x = x * l) → x ∈ Zt := by
    rw [hUt, hZt]
    rintro _ ⟨u, hu, rfl⟩ hcomm
    refine ⟨u, hCLU u hu fun l hl => ?_, rfl⟩
    have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htL l).mp hl
    have h1 := hcomm _ hl'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have h2 : t * (l * u) * t⁻¹ = t * (u * l) * t⁻¹ := by
      calc t * (l * u) * t⁻¹ = t * l * t⁻¹ * (t * u * t⁻¹) := by group
        _ = t * u * t⁻¹ * (t * l * t⁻¹) := h1
        _ = t * (u * l) * t⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hZtCU : Zt ≤ Subgroup.centralizer (blockU K : Set G) :=
    Sp4Z.le_centralizer_of_inf_eq_bot (fun _ hz => hSU (hUtS (hZtU hz)))
      (fun _ hu => hSZt (hUS hu)) hLZt hCLU hZZt
  have hZCUt : blockZ K ≤ Subgroup.centralizer (Ut : Set G) :=
    Sp4Z.le_centralizer_of_inf_eq_bot (fun _ hz => hSUt (hUS (hZU hz)))
      (fun _ hu => hSZ (hUtS hu)) hLZ hCLUt (by rw [inf_comm]; exact hZZt)
  have hUtC : ¬ Ut ≤ Subgroup.centralizer (blockU K : Set G) := by
    rw [hUt]
    exact sk.not_map_conj_blockU_le_centralizer hR hC h37 h38 h39 hchar hmat
  have hQC : Q ≤ Subgroup.centralizer (blockU K : Set G) :=
    Subgroup.le_centralizer_iff.mp (hshort.2.2.1.1.trans inf_le_right)
  have hV₁tC : V₁t ≤ Subgroup.centralizer (blockU K : Set G) := by
    rw [hV₁t']
    exact _root_.sup_le (hVU.trans (hUQ.trans hQC)) hZtCU
  have hUtCUt : Ut ≤ Subgroup.centralizer (Ut : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hUtab y hy x hx
  have hG1 : (blockU K) ⊓ Ut ≤ V₁ := by
    by_contra hnot
    set U₁ := ((blockU K) ⊓ Ut) ⊔ blockZ K with hU₁
    have hV₁U₁ : V₁ ≤ U₁ := sup_le_sup_right (le_inf hVU hVUt) _
    have hLU₁ : L ≤ Subgroup.normalizer (U₁ : Set G) := by
      intro l hl
      apply mem_normalizer_of_map_conj_le
      rw [hU₁, Subgroup.map_sup,
        map_conj_eq_of_mem_normalizer (mem_normalizer_inf (hLU hl) (hLUt hl)),
        map_conj_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ (hLZ hl))]
    have h1 := hIrr U₁ hV₁U₁ (_root_.sup_le inf_le_left hZU) hLU₁
      (fun h => hnot (le_sup_left.trans h))
    apply hUtC
    rw [Subgroup.le_centralizer_iff, ← h1, hU₁]
    exact _root_.sup_le (inf_le_right.trans hUtCUt) hZCUt
  have hG2 : Ut ⊓ Q ≤ V₁t := by
    set U₁ := ((blockU K) ⊓ Q.comap (MulAut.conj t).toMonoidHom) ⊔ blockZ K with hU₁
    have hV₁U₁ : V₁ ≤ U₁ := sup_le_sup_right (fun v hv =>
      ⟨hVU hv, hUQ (hVU ((Subgroup.mem_normalizer_iff.mp htV v).mp hv))⟩) _
    have hLU₁ : L ≤ Subgroup.normalizer (U₁ : Set G) := by
      intro l hl
      apply mem_normalizer_of_map_conj_le
      rw [hU₁, Subgroup.map_sup,
        map_conj_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ (hLZ hl))]
      refine sup_le_sup_right ?_ _
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
    have hU₁V : U₁ ≤ V₁ := by
      by_contra hnot
      have h1 := hIrr U₁ hV₁U₁ (_root_.sup_le inf_le_left hZU) hLU₁ hnot
      have hle : U₁ ≤
          (Subgroup.centralizer (blockU K : Set G)).comap (MulAut.conj t).toMonoidHom := by
        rw [hU₁]
        refine _root_.sup_le (fun x hx => hQC hx.2) (fun z hz => hZtCU ?_)
        rw [hZt]
        exact ⟨z, hz, rfl⟩
      apply hUtC
      rw [hUt]
      rintro _ ⟨u, hu, rfl⟩
      have hu1 : u ∈ U₁ := h1 ▸ hu
      exact hle hu1
    rw [hUt, hV₁t]
    rintro _ ⟨⟨u, hu, rfl⟩, hxQ⟩
    exact ⟨u, hU₁V (Subgroup.mem_sup_left ⟨hu, hxQ⟩), rfl⟩
  have hULV : ⁅(blockU K), L⁆ ⊔ V₁ = (blockU K) := by
    by_contra hne
    have hle : ⁅(blockU K), L⁆ ⊔ V₁ ≤ (blockU K) :=
      _root_.sup_le (commutator_le_left_of_le_normalizer hLU) hV₁U
    have hLN : L ≤ Subgroup.normalizer ((⁅(blockU K), L⁆ ⊔ V₁ : Subgroup G) : Set G) := by
      intro l hl
      apply mem_normalizer_of_map_conj_le
      rw [Subgroup.map_sup,
        map_conj_eq_of_mem_normalizer (Subgroup.normalizer_commutator_ge_right (blockU K) L hl),
        map_conj_eq_of_mem_normalizer (hLV₁ l hl)]
    have h1 : ⁅(blockU K), L⁆ ⊔ V₁ ≤ V₁ := by
      by_contra hnot
      exact hne (hIrr _ le_sup_right hle hLN hnot)
    have hUV : (blockU K) ≤ V₁ := fun u hu => hfixU u hu fun l hl =>
      h1 (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu hl))
    have hWtop : W = ⊤ := by
      rw [eq_top_iff]
      intro w _
      obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd w)
      have := (hWiff u).mp (hUV u.2)
      rwa [hu, toAdd_ofAdd] at this
    rw [hWtop, finrank_top, Module.finrank_fintype_fun_eq_card] at hW
    simp at hW
  have hUtLV : Ut = ⁅Ut, L⁆ ⊔ V₁t := by
    rw [hUt, hV₁t]
    conv_lhs => rw [← hULV]
    rw [Subgroup.map_sup, Subgroup.map_commutator, hLt]
  have hUtLK : ⁅Ut, L⁆ ≤ Ut ⊓ K :=
    le_inf (commutator_le_left_of_le_normalizer hLUt)
      ((commutator_le_right_of_le_normalizer
        (hUtS.trans (inf_le_left.trans (sk.base.hyp.T_le.trans sk.base.hyp.normal)))).trans hLK)
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
    have huV : (u : G) ∈ V₁ := (hWiff u).mpr (by rw [hu, toAdd_ofAdd]; exact hw)
    have hV₁k : V₁ ≤ Subgroup.centralizer ({(k : G)} : Set G) := by
      rw [hV₁]
      refine _root_.sup_le (fun v hv => ?_) (fun z hz => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact hUtab _ hk _ (hVUt hv)
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact Subgroup.mem_centralizer_iff.mp (hZC hz) _ k.2
    have hcomm : (u : G) = k * u * (k : G)⁻¹ := by
      rw [Subgroup.mem_centralizer_iff.mp (hV₁k huV) k rfl, mul_inv_cancel_right]
    have h1 : Multiplicative.toAdd (β u) =
        (αG k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ Multiplicative.toAdd (β u) :=
      hequiv k u u hcomm
    rw [hu, toAdd_ofAdd] at h1
    exact h1.symm
  have hUtU : ⁅Ut, blockU K⁆ ≤ V₁ :=
    (le_inf (commutator_le_right_of_le_normalizer (hUtS.trans hSU))
      (commutator_le_left_of_le_normalizer (hUS.trans hSUt))).trans hG1
  have hX2 : ∀ x ∈ X, ∀ v, (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v - v ∈ W := by
    intro x hx v
    obtain ⟨k, hk, rfl⟩ := hXmem x hx
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd v)
    let c : blockU K := ⟨k * u * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU k.2) u).mp u.2⟩
    have h1 : Multiplicative.toAdd (β c) =
        (αG k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ Multiplicative.toAdd (β u) :=
      hequiv k u c rfl
    rw [hu, toAdd_ofAdd] at h1
    have h2 : ((c * u⁻¹ : blockU K) : G) ∈ V₁ := by
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
    apply hUtC
    rw [hUtLV]
    refine _root_.sup_le (fun x hx => hQC ?_) hV₁tC
    obtain ⟨hxUt, hxK⟩ := hUtLK hx
    have h1 := hmemX ⟨x, hxK⟩ hxUt
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hxK⟩ : K) ∈ α.ker := MonoidHom.mem_ker.mpr (Subtype.ext h1)
    rw [hkerα] at h2
    exact (mem_pCoreOf_iff' _).mpr h2
  have hXC : ∀ x ∈ X, (∀ l : L, f l * x = x * f l) → x = 1 := by
    intro x hx hc
    obtain ⟨k, hk, rfl⟩ := hXmem x hx
    have hkV : (k : G) ∈ V₁t := by
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
    have hkQ : (k : G) ∈ Q := Sp4Z.mem_pCoreOf_of_mem_centralizer hmat k (hV₁tC hkV)
    have h1 : k ∈ α.ker := by
      rw [hkerα]
      exact (mem_pCoreOf_iff' k).mp hkQ
    change ((α k : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) = 1
    rw [MonoidHom.mem_ker.mp h1]
    rfl
  exact hd.false_of_radical X hXS hX1 hX2 hXN hXne hXC

end Setting432K

theorem gap437Sp4Z_of (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) : Gap437Sp4Z :=
  fun _ _ _ _ _ _ _ _ _ _ _ sk hchar _ hc2 =>
    (sk.false_of_sp4Case2 hR hC h37 h38 h39 hchar hc2).elim

end CFSG.Quasithin.H13.Ch4
