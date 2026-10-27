module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDJ
public import CFSG.Milestones.ASVolI.C61.PAppDCls3

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppD

open CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.burnsideC56_P.AppC
open CFSG.QuasithinUnique.AppC hiding Cfg Cfg.D_le_Q Cfg.Q_comm_U Cfg.Q_eq Cfg.S_le_N_D
  Cfg.UD_unique Cfg.U_comm_D Cfg.U_inf_D Cfg.aU_spec Cfg.blockU_le_baum Cfg.card_Q Cfg.card_U
  Cfg.conj_mem_blockD Cfg.exists_UD Cfg.hL Cfg.hQ Cfg.hQS Cfg.hSH Cfg.hSN Cfg.hU Cfg.hUQ Cfg.hUS
  Cfg.im_le_Dstd Cfg.mem_Q_iff Cfg.mem_Q_of_pf_eq_one Cfg.omegaOneCenter_le_pCoreOf
  Cfg.pf_eq_one_of_mem_Q Mate.B_eq Mate.B_eq_sup Mate.B_le_sup Mate.D_comm_V Mate.D_elem
  Mate.D_inf_conj Mate.D_le_B Mate.D_le_K Mate.D_le_of_isMax Mate.G_spec Mate.J_eq_B Mate.Q_elem
  Mate.Q_isMax Mate.Q_le_B Mate.Qx_isMax Mate.S_le_N_V Mate.V_comm Mate.V_conj Mate.V_elem
  Mate.V_inf_Q_le_U Mate.V_le_B Mate.V_le_S Mate.V_not_le_Q Mate.V_sq Mate.X'_spec Mate.Yv_isMax
  Mate.Yv_le Mate.baumD_eq Mate.card_V Mate.card_eq_Q Mate.card_symm Mate.cent_U_V Mate.conj_K
  Mate.eq_Q_of_type_bot Mate.eq_Yv_of_type_t1 Mate.exists_vud Mate.fixU_le_of_isMax Mate.fix_mem
  Mate.im_V Mate.pf_ne_one Mate.sqSub_D Mate.sqSub_K Mate.type_cases a5_core a5_core_std
  blockD_le_pCoreOf blockQ_comm_pCoreOf blockU_inf_blockD card_im_S exists_mem_thompsonJ_pi_ne_one
  exists_split exists_split' nonempty_cfg pCoreOf_comm_blockU pCoreOf_eq_blockU_sup_blockD
  swapGen_imJ

variable {G : Type} [Group G] [Finite G]

namespace GMate
open CFSG.QuasithinUnique.AppD.GMate

variable {T M H S L M₀ : Subgroup G} {a : G} (C : GCfg T M H S L) (m : GMate S T M₀ a)
include C m

theorem C_D_a {δ : G} (hδ : δ ∈ blockD S L) (h : a * δ * a⁻¹ = δ) : δ = 1 := by
  have h1 : δ ∈ conjR (blockD S L) a := by
    show δ ∈ conjSubgroup (blockD S L) a
    rw [mem_conjSubgroup_iff, h]; exact hδ
  have h2 : δ ∈ blockD S L ⊓ conjR (blockD S L) a := ⟨hδ, h1⟩
  rw [GMate.D_inf_conj (m := m) C, Subgroup.mem_bot] at h2
  exact h2

theorem C_Q_a_decomp {q : G} (hq : q ∈ pCoreOf 2 H) (h : a * q * a⁻¹ = q) :
    ∃ f ∈ C.U ⊓ conjR (C.U) a, ∃ δ ∈ blockD S L, q = f * δ := by
  obtain ⟨u, hu, δ, hδ, hqud⟩ := C.exists_UD hq
  have hqQ' : q ∈ conjR (pCoreOf 2 H) a := by
    show q ∈ conjSubgroup (pCoreOf 2 H) a
    rw [mem_conjSubgroup_iff, h]; exact hq
  rw [GMate.Qx_eq (m := m) C] at hqQ'
  obtain ⟨v, hv, δ', hδ', hqvd⟩ := C5.mem_sup_of_commute
    (fun v hv d hd => (GMate.D_comm_V (m := m) C hd hv).symm) hqQ'
  have hvS : v ∈ S := GMate.V_le_S (m := m) C hv
  have heq : u * δ = v * δ' := by rw [← hqud, ← hqvd]
  have h1 : v⁻¹ * u = δ' * δ⁻¹ := by
    calc v⁻¹ * u = v⁻¹ * (u * δ) * δ⁻¹ := by group
      _ = v⁻¹ * (v * δ') * δ⁻¹ := by rw [heq]
      _ = δ' * δ⁻¹ := by group
  have hD : v⁻¹ * u ∈ blockD S L := by
    rw [h1]; exact (blockD S L).mul_mem hδ' ((blockD S L).inv_mem hδ)
  have hQ1 : v⁻¹ * u ∈ pCoreOf 2 H := C.D_le_Q hD
  have hvQ : v ∈ pCoreOf 2 H := by
    have := mul_mem hQ1 (inv_mem (C.hUQ hu))
    simpa using this
  have hvU : v ∈ C.U := GMate.V_inf_Q_le_U (m := m) C hv hvQ
  have hvuU : v⁻¹ * u ∈ C.U := (C.U).mul_mem ((C.U).inv_mem hvU) hu
  have hvu : v⁻¹ * u ∈ C.U ⊓ blockD S L := ⟨hvuU, hD⟩
  rw [C.U_inf_D, Subgroup.mem_bot] at hvu
  have huv : u = v := by
    calc u = v * (v⁻¹ * u) := by group
      _ = v := by rw [hvu, mul_one]
  have hδδ : δ = δ' := by
    rw [huv] at heq
    exact mul_left_cancel heq
  refine ⟨u, ⟨hu, huv ▸ hv⟩, δ, hδ, hqud⟩

theorem card_KQ_le {K₀ : Subgroup G} (hK₀S : K₀ ≤ S) (hK₀a : ∀ k ∈ K₀, a * k * a⁻¹ = k)
    (hK₀ab : ∀ k ∈ K₀, ∀ k' ∈ K₀, k * k' = k' * k) :
    Nat.card ↥(K₀ ⊓ pCoreOf 2 H) ≤
      Nat.card ↥(C.U ⊓ conjR (C.U) a ⊓ Subgroup.centralizer (K₀ : Set G)) := by
  classical
  have hdec : ∀ q : ↥(K₀ ⊓ pCoreOf 2 H), ∃ f, f ∈ C.U ⊓ conjR (C.U) a ∧
      f ∈ Subgroup.centralizer (K₀ : Set G) ∧ ∃ δ ∈ blockD S L, (q : G) = f * δ := by
    intro q
    obtain ⟨f, hf, δ, hδ, hqfd⟩ := GMate.C_Q_a_decomp (m := m) C q.2.2 (hK₀a q q.2.1)
    refine ⟨f, hf, ?_, δ, hδ, hqfd⟩
    refine Subgroup.mem_centralizer_iff.2 fun s hs => ?_
    have hsS : s ∈ S := hK₀S hs
    have hsq : s * (q : G) * s⁻¹ = q := by rw [hK₀ab s hs q q.2.1]; group
    have hsf : s * f * s⁻¹ ∈ C.U := C.P.conj_mem_U (hsS) hf.1
    have hsδ : s * δ * s⁻¹ ∈ blockD S L := GCfg.conj_mem_blockD hsS hδ
    have h1 : (s * f * s⁻¹) * (s * δ * s⁻¹) = f * δ := by
      calc (s * f * s⁻¹) * (s * δ * s⁻¹) = s * (f * δ) * s⁻¹ := by group
        _ = f * δ := by rw [← hqfd]; exact hsq
    have h2 := C.UD_unique hsf hf.1 hsδ hδ h1
    calc s * f = (s * f * s⁻¹) * s := by group
      _ = f * s := by rw [h2.1]
  choose f hfF hfC δ hδ hq using hdec
  let g : ↥(K₀ ⊓ pCoreOf 2 H) →
      ↥(C.U ⊓ conjR (C.U) a ⊓ Subgroup.centralizer (K₀ : Set G)) :=
    fun q => ⟨f q, hfF q, hfC q⟩
  refine Nat.card_le_card_of_injective g fun q₁ q₂ h => ?_
  have hf : f q₁ = f q₂ := congrArg Subtype.val h
  have e1 := hq q₁
  have e2 := hq q₂
  rw [hf] at e1
  have hqq : (q₁ : G)⁻¹ * q₂ = (δ q₁)⁻¹ * δ q₂ := by
    rw [e1, e2]; group
  have hδD : (δ q₁)⁻¹ * δ q₂ ∈ blockD S L :=
    (blockD S L).mul_mem ((blockD S L).inv_mem (hδ q₁)) (hδ q₂)
  have hfix : a * ((δ q₁)⁻¹ * δ q₂) * a⁻¹ = (δ q₁)⁻¹ * δ q₂ := by
    rw [← hqq]
    have h1 := hK₀a q₁ q₁.2.1
    have h2 := hK₀a q₂ q₂.2.1
    calc a * ((q₁ : G)⁻¹ * q₂) * a⁻¹ = (a * q₁ * a⁻¹)⁻¹ * (a * q₂ * a⁻¹) := by group
      _ = (q₁ : G)⁻¹ * q₂ := by rw [h1, h2]
  have h1' := GMate.C_D_a (m := m) C hδD hfix
  have hδeq : δ q₁ = δ q₂ := by
    calc δ q₁ = δ q₁ * ((δ q₁)⁻¹ * δ q₂) := by rw [h1']; group
      _ = δ q₂ := by group
  apply Subtype.ext
  rw [e1, e2, hδeq]

theorem z_not_mem {s : G} (hsS : s ∈ S) (hsa : a * s * a⁻¹ = s) (hs2 : s * s = 1) :
    C.P.pf s ≠ zA := by
  intro hz
  have hzE : zA ∈ Eset := (mem_Eset_iff _).2 (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨v, hv, u, hu, δ, hδ, hsvud, hpv⟩ := GMate.exists_vud (m := m) C hsS (by rw [hz]; exact hzE)
  have hvS : v ∈ S := GMate.V_le_S (m := m) C hv
  have hδvu : δ * (v * u) = (v * u) * δ := by
    have h1 := GMate.D_comm_V (m := m) C hδ hv
    have h2 := C.U_comm_D hu hδ
    calc δ * (v * u) = (δ * v) * u := by group
      _ = (v * δ) * u := by rw [h1]
      _ = v * (δ * u) := by group
      _ = v * (u * δ) := by rw [← h2]
      _ = (v * u) * δ := by group
  have hδ2 : δ * δ = 1 := by
    have := (GMate.D_elem (m := m) C).2 δ hδ
    rwa [pow_two] at this
  have hvu2 : (v * u) * (v * u) = 1 := by
    have h := hs2
    rw [hsvud] at h
    calc (v * u) * (v * u) = (v * u) * (v * u) * (δ * δ) := by rw [hδ2, mul_one]
      _ = (v * u * δ) * (v * u * δ) := by
        calc (v * u) * (v * u) * (δ * δ) = (v * u) * ((v * u) * δ) * δ := by group
          _ = (v * u) * (δ * (v * u)) * δ := by rw [hδvu]
          _ = (v * u * δ) * (v * u * δ) := by group
      _ = 1 := h
  have hcomm : v * u = u * v := comm_of_sq (by rw [pow_two]; exact hvu2)
    (V_sq (x := a) C hv) (C.hU.2 u hu)
  have hfix : vact (C.P.pf v) (C.P.bf u) = C.P.bf u := (C.P.comm_iff (hvS) hu).1 hcomm
  rw [hpv, hz] at hfix
  have hall : ∀ σ ∈ Eset, vact σ (C.P.bf u) = C.P.bf u := fun σ hσ =>
    Subtype.ext (fixz_all _ (congrArg Subtype.val hfix) σ hσ)
  have hVN : conjR (C.U) a ≤ S := (GMate.V_le_S (m := m) C)
  have huC : u ∈ Subgroup.centralizer (conjR (C.U) a : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
    have hwE : C.P.pf w ∈ Eset := by
      have : C.P.pf w ∈ C.P.im (conjR (C.U) a) := (C.P.mem_im_pf hVN).2 ⟨w, hw, rfl⟩
      rw [GMate.im_V (m := m) C] at this
      exact (mem_Estd _).1 this
    exact (C.P.comm_iff (hVN hw) hu).2 (hall _ hwE)
  have huV : u ∈ conjR (C.U) a := by
    have : u ∈ C.U ⊓ Subgroup.centralizer (conjR (C.U) a : Set G) := ⟨hu, huC⟩
    rw [(GMate.cent_U_V (m := m) C).1] at this
    exact this.2
  have hsQ' : s ∈ conjR (pCoreOf 2 H) a := by
    rw [GMate.Qx_eq (m := m) C, hsvud]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem hv huV)) (Subgroup.mem_sup_right hδ)
  have hsQ : s ∈ pCoreOf 2 H := by
    have : a * s * a⁻¹ ∈ pCoreOf 2 H := mem_conjSubgroup_iff.1 hsQ'
    rwa [hsa] at this
  have h1 := C.pf_eq_one_of_mem_Q hsQ
  rw [hz] at h1
  exact zA_ne_one h1

theorem card_F_cent_le_two {s : G} (hsS : s ∈ S) (hsE : C.P.pf s ∉ Eset) :
    Nat.card ↥(C.U ⊓ conjR (C.U) a ⊓ Subgroup.centralizer ({s} : Set G)) ≤ 2 := by
  classical
  have hVN : conjR (C.U) a ≤ S := (GMate.V_le_S (m := m) C)
  have hsD : C.P.pf s ∈ Dset := by
    have : C.P.pf s ∈ C.P.im S := (C.P.mem_im_pf le_rfl).2 ⟨s, hsS, rfl⟩
    rw [C.hS] at this
    exact (mem_Dstd _).1 this
  have hkey : ∀ x : G, x ∈ C.U ⊓ conjR (C.U) a ⊓ Subgroup.centralizer ({s} : Set G) →
      (C.P.bf x).1 = 0 ∨ (C.P.bf x).1 = ![1, 1, 1, 1, 0] := by
    intro x hx
    obtain ⟨⟨hfU, hfV⟩, hfs⟩ := hx
    have hfC : x ∈ Subgroup.centralizer (conjR (C.U) a : Set G) := by
      have : x ∈ C.U ⊓ conjR (C.U) a := ⟨hfU, hfV⟩
      rw [← (GMate.cent_U_V (m := m) C).1] at this
      exact this.2
    have hallE : ∀ σ ∈ Eset, vact σ (C.P.bf x) = C.P.bf x := by
      intro σ hσ
      have hσV : σ ∈ C.P.im (conjR (C.U) a) := by
        rw [GMate.im_V (m := m) C]; exact (mem_Estd σ).2 hσ
      obtain ⟨y, hy, rfl⟩ := (C.P.mem_im_pf hVN).1 hσV
      exact (C.P.comm_iff (hVN hy) hfU).1 (Subgroup.mem_centralizer_iff.1 hfC y hy)
    have hs' : vact (C.P.pf s) (C.P.bf x) = C.P.bf x :=
      (C.P.comm_iff (hsS) hfU).1 (Subgroup.mem_centralizer_iff.1 hfs s rfl)
    exact fixF_of_ne _ hsD hsE _ ((mem_evenWeight_iff _).1 (C.P.bf x).2)
      (fun σ hσ => congrArg Subtype.val (hallE σ hσ)) (congrArg Subtype.val hs')
  let g : ↥(C.U ⊓ conjR (C.U) a ⊓ Subgroup.centralizer ({s} : Set G)) → Bool :=
    fun f => decide ((C.P.bf (f : G)).1 = 0)
  have hg : Function.Injective g := by
    intro f₁ f₂ h
    have hmem : ∀ f : ↥(C.U ⊓ conjR (C.U) a ⊓ Subgroup.centralizer ({s} : Set G)),
        (f : G) ∈ C.U := fun f => f.2.1.1
    apply Subtype.ext
    apply C.P.bf_inj (hmem f₁) (hmem f₂)
    apply Subtype.ext
    simp only [g, decide_eq_decide] at h
    rcases hkey f₁ f₁.2 with h1 | h1 <;> rcases hkey f₂ f₂.2 with h2 | h2
    · rw [h1, h2]
    · exfalso
      have := h.1 h1
      rw [h2] at this
      exact absurd (congrFun this 0) (by decide)
    · exfalso
      have := h.2 h2
      rw [h1] at this
      exact absurd (congrFun this 0) (by decide)
    · rw [h1, h2]
  have := Nat.card_le_card_of_injective g hg
  simpa using this

theorem no_t_commuting (hD1 : blockD S L = ⊥) (ha2 : a * a = 1) {s : G} (hsS : s ∈ S)
    (hsa : a * s * a⁻¹ = s) (hs2 : s * s = 1)
    (hF : ∀ f ∈ C.U ⊓ conjR (C.U) a, a * f * a⁻¹ = f)
    (ht : C.P.pf s = swap 0 1 ∨ C.P.pf s = swap 2 3) : False := by
  have hVN : conjR (C.U) a ≤ S := (GMate.V_le_S (m := m) C)
  have hsN : s ∈ S := hsS
  have hsE : C.P.pf s ∈ Eset := by
    rcases ht with h | h
    · rw [h]; exact t1_mem_Eset
    · rw [h]; exact t2_mem_Eset
  obtain ⟨v, hv, u, hu, δ, hδ, hsvud, hpv⟩ := GMate.exists_vud (m := m) C hsS hsE
  have hδ1 : δ = 1 := by
    rw [hD1] at hδ
    exact Subgroup.mem_bot.1 hδ
  rw [hδ1, mul_one] at hsvud
  have hvS : v ∈ S := GMate.V_le_S (m := m) C hv
  have hvu2 : (v * u) * (v * u) = 1 := by rw [← hsvud]; exact hs2
  have hcomm : v * u = u * v := comm_of_sq (by rw [pow_two]; exact hvu2)
    (V_sq (x := a) C hv) (C.hU.2 u hu)
  have hy : vact (C.P.pf v) (C.P.bf u) = C.P.bf u := (C.P.comm_iff (hvS) hu).1 hcomm
  rw [hpv] at hy
  obtain ⟨w, hwU, hbw⟩ := C.P.bf_surj ⟨![1, 0, 1, 0, 0], (mem_evenWeight_iff _).2 even_e0e2⟩
  have hwS : w ∈ S := C.hUS hwU
  have hwN : w ∈ S := hwS
  have hwinv : w⁻¹ = w := inv_eq_self_of_sq (C.hU.2 w hwU)
  have huinv : u⁻¹ = u := inv_eq_self_of_sq (C.hU.2 u hu)
  have huw : u * w = w * u := (C5.isElemAbelian_two_iff.1 C.hU).1 _ hu _ hwU
  set f : G := s * w * s⁻¹ * w with hf
  have hsw : s * w * s⁻¹ = v * w * v⁻¹ := by
    rw [hsvud]
    calc v * u * w * (v * u)⁻¹ = v * (u * w * u⁻¹) * v⁻¹ := by group
      _ = v * w * v⁻¹ := by rw [huw]; group
  have hswU : s * w * s⁻¹ ∈ C.U := C.P.conj_mem_U hsN hwU
  have hfU : f ∈ C.U := (C.U).mul_mem hswU hwU
  have hfV : f ∈ conjR (C.U) a := by
    have h1 : w * v⁻¹ * w⁻¹ ∈ conjR (C.U) a :=
      (Subgroup.mem_normalizer_iff.1 (GMate.S_le_N_V (m := m) C hwS) v⁻¹).1 ((conjR (C.U) a).inv_mem hv)
    have e : f = v * (w * v⁻¹ * w⁻¹) := by
      rw [hf, hsw, hwinv]; group
    rw [e]
    exact (conjR (C.U) a).mul_mem hv h1
  have hbf : C.P.bf f = vact (C.P.pf s) (C.P.bf w) + C.P.bf w := by
    rw [hf, C.P.bf_mul hswU hwU, C.P.bf_conj hsN hwU]
  have hw' : a * w * a⁻¹ ∈ conjR (C.U) a := by
    show a * w * a⁻¹ ∈ conjSubgroup (C.U) a
    rw [mem_conjSubgroup_iff]
    have : a * (a * w * a⁻¹) * a⁻¹ = w := by
      calc a * (a * w * a⁻¹) * a⁻¹ = (a * a) * w * (a * a)⁻¹ := by group
        _ = w := by rw [ha2]; group
    rw [this]; exact hwU
  set w' : G := a * w * a⁻¹ with hw'def
  have hw'S : w' ∈ S := GMate.V_le_S (m := m) C hw'
  have hw'N : w' ∈ S := hw'S
  have hw'inv : w'⁻¹ = w' := inv_eq_self_of_sq (V_sq (x := a) C hw')
  have hfa : a * f * a⁻¹ = f := hF f ⟨hfU, hfV⟩
  have hfa' : a * f * a⁻¹ = s * w' * s⁻¹ * w' := by
    have e : a * f * a⁻¹ = (a * s * a⁻¹) * (a * w * a⁻¹) * (a * s * a⁻¹)⁻¹ * (a * w * a⁻¹) := by
      rw [hf]; group
    rw [e, hsa]
  have hx₀ : u * w' * u⁻¹ ∈ conjR (C.U) a :=
    (Subgroup.mem_normalizer_iff.1 (GMate.S_le_N_V (m := m) C (C.hUS hu)) w').1 hw'
  have hsw' : s * w' * s⁻¹ = u * w' * u⁻¹ := by
    have hcv : v * (u * w' * u⁻¹) = (u * w' * u⁻¹) * v := V_comm (x := a) C hv hx₀
    rw [hsvud]
    calc v * u * w' * (v * u)⁻¹ = v * (u * w' * u⁻¹) * v⁻¹ := by group
      _ = (u * w' * u⁻¹) * v * v⁻¹ := by rw [hcv]
      _ = u * w' * u⁻¹ := by group
  have hk : f = u * w' * u⁻¹ * w' := by
    rw [← hfa, hfa', hsw']
  have hw'uU : w' * u⁻¹ * w'⁻¹ ∈ C.U := C.P.conj_mem_U hw'N ((C.U).inv_mem hu)
  have hbk : C.P.bf f = C.P.bf u + vact (C.P.pf w') (C.P.bf u) := by
    have e : f = u * (w' * u⁻¹ * w'⁻¹) := by
      rw [hk, hw'inv]; group
    rw [e, C.P.bf_mul hu hw'uU, C.P.bf_conj hw'N ((C.U).inv_mem hu), huinv]
  have hσ' : C.P.pf w' ∈ Eset := by
    have : C.P.pf w' ∈ C.P.im (conjR (C.U) a) := (C.P.mem_im_pf hVN).2 ⟨w', hw', rfl⟩
    rw [GMate.im_V (m := m) C] at this
    exact (mem_Estd _).1 this
  have hrel := hbf.symm.trans hbk
  rw [hbw] at hrel
  have hrel' := congrArg Subtype.val hrel
  exact X_contra (C.P.bf u).1 _ hσ' (C.P.pf s) ht (congrArg Subtype.val hy) hrel'

theorem card_lt_Q {A' : Subgroup G} (hA' : IsElemAbelian 2 A') (hA'M : A' ≤ M₀) (haA : a ∈ A') :
    Nat.card ↥A' < Nat.card ↥(pCoreOf 2 H) := by
  classical
  have ha2 : a * a = 1 := by
    have := hA'.2 a haA
    rwa [pow_two] at this
  set K₀ : Subgroup G := A' ⊓ S with hK₀
  have hK₀S : K₀ ≤ S := inf_le_right
  have hK₀N : K₀ ≤ S := hK₀S
  have hK₀ab : ∀ k ∈ K₀, ∀ k' ∈ K₀, k * k' = k' * k := fun k hk k' hk' =>
    B2F.isElemAbelian_comm hA' hk.1 hk'.1
  have hK₀a : ∀ k ∈ K₀, a * k * a⁻¹ = k := fun k hk => by
    have := B2F.isElemAbelian_comm hA' haA hk.1
    calc a * k * a⁻¹ = (k * a) * a⁻¹ := by rw [this]
      _ = k := by group
  have hK₀2 : ∀ k ∈ K₀, k * k = 1 := fun k hk => by
    have := hA'.2 k hk.1
    rwa [pow_two] at this
  have hidx : (A' ⊓ S).relIndex A' ≤ 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    have h2 : S.relIndex M₀ ≠ 0 := by rw [m.h2]; norm_num
    have := Subgroup.relIndex_le_of_le_right hA'M h2
    rwa [m.h2] at this
  have hA'card : Nat.card ↥A' ≤ 2 * Nat.card ↥K₀ := by
    have h := C5.card_eq_card_mul_relIndex (inf_le_left : A' ⊓ S ≤ A')
    calc Nat.card ↥A' = Nat.card ↥K₀ * (A' ⊓ S).relIndex A' := h
      _ ≤ Nat.card ↥K₀ * 2 := Nat.mul_le_mul_left _ hidx
      _ = 2 * Nat.card ↥K₀ := by ring
  have hKQ : K₀ ⊓ Subgroup.centralizer (C.U : Set G) = K₀ ⊓ pCoreOf 2 H := by
    ext k
    constructor
    · rintro ⟨hkA, hkC⟩
      exact ⟨hkA, by rw [← C.hQ]; exact ⟨C.hSH (hK₀S hkA), hkC⟩⟩
    · rintro ⟨hkA, hkQ⟩
      exact ⟨hkA, Subgroup.mem_centralizer_iff.2 fun u hu => (C.Q_comm_U hkQ hu).symm⟩
  have hcard1 := C.P.card_im_mul hK₀N
  rw [hKQ] at hcard1
  have hKQ4 : Nat.card ↥(K₀ ⊓ pCoreOf 2 H) ≤ 4 := by
    have h1 := GMate.card_KQ_le (m := m) C hK₀S hK₀a hK₀ab
    have h2 : Nat.card ↥(C.U ⊓ conjR (C.U) a ⊓ Subgroup.centralizer (K₀ : Set G)) ≤
        Nat.card ↥(C.U ⊓ conjR (C.U) a) := Subgroup.card_le_of_le inf_le_left
    have h3 := (GMate.cent_U_V (m := m) C).2.2
    omega
  have hPD : C.P.im K₀ ≤ Dstd := by
    rw [← C.hS]; exact C.P.im_mono hK₀S
  have hKel : IsElemAbelian 2 K₀ := B2F.isElemAbelian_mono inf_le_left hA'
  have hPe := C.P.im_elemAbelian hKel
  have hzP : zA ∉ C.P.im K₀ := by
    intro hz
    obtain ⟨s, hs, hsz⟩ := (C.P.mem_im_pf hK₀N).1 hz
    exact GMate.z_not_mem (m := m) C (hK₀S hs) (hK₀a s hs) (hK₀2 s hs) hsz
  have hP2 : Nat.card ↥(C.P.im K₀) ≤ 2 := card_le_two_of_not_mem_z _ hPD hPe.1 hPe.2 hzP
  have hprod : Nat.card ↥(C.P.im K₀) * Nat.card ↥(K₀ ⊓ pCoreOf 2 H) ≤ 2 * 4 :=
    Nat.mul_le_mul hP2 hKQ4
  have hK8 : Nat.card ↥K₀ ≤ 8 := by rw [← hcard1]; omega
  have hQcard := C.card_Q
  have hdpos : 0 < Nat.card ↥(blockD S L) := Nat.card_pos
  by_cases hd1 : Nat.card ↥(blockD S L) = 1
  ·
    have hD1 : blockD S L = ⊥ := Subgroup.card_eq_one.1 hd1
    by_contra hge
    push Not at hge
    have hK8' : 8 ≤ Nat.card ↥K₀ := by omega
    have hpos : 0 < Nat.card ↥(C.P.im K₀) := Nat.card_pos
    have hpq : Nat.card ↥(C.P.im K₀) = 2 ∧ Nat.card ↥(K₀ ⊓ pCoreOf 2 H) = 4 := by
      rw [← hcard1] at hK8'
      generalize Nat.card ↥(C.P.im K₀) = p at hP2 hpos hK8' ⊢
      generalize Nat.card ↥(K₀ ⊓ pCoreOf 2 H) = q at hKQ4 hK8' ⊢
      interval_cases p <;> interval_cases q <;> omega
    have hKQF : K₀ ⊓ pCoreOf 2 H ≤ C.U ⊓ conjR (C.U) a := by
      intro q hq
      obtain ⟨f, hf, δ, hδ, hqfd⟩ := GMate.C_Q_a_decomp (m := m) C hq.2 (hK₀a q hq.1)
      rw [hD1, Subgroup.mem_bot] at hδ
      rw [hqfd, hδ, mul_one]
      exact hf
    have hKQeq : K₀ ⊓ pCoreOf 2 H = C.U ⊓ conjR (C.U) a :=
      Subgroup.eq_of_le_of_card_ge hKQF (by rw [(GMate.cent_U_V (m := m) C).2.2]; omega)
    have hF : ∀ f ∈ C.U ⊓ conjR (C.U) a, a * f * a⁻¹ = f := fun f hf => by
      rw [← hKQeq] at hf
      exact hK₀a f hf.1
    have hPne : C.P.im K₀ ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot _).1 (by omega)
    obtain ⟨σ', hσ'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hPne
    have hσ'1 : (σ' : Perm (Fin 5)) ≠ 1 := fun h => hσ' (Subtype.ext h)
    obtain ⟨s, hsK, hsσ⟩ := (C.P.mem_im_pf hK₀N).1 σ'.2
    by_cases hσE : (σ' : Perm (Fin 5)) ∈ Eset
    · rcases (mem_Eset_iff _).1 hσE with h | h | h | h
      · exact hσ'1 h
      · exact GMate.no_t_commuting (m := m) C hD1 ha2 (hK₀S hsK) (hK₀a s hsK) (hK₀2 s hsK) hF
          (Or.inl (by rw [hsσ]; exact h))
      · exact GMate.no_t_commuting (m := m) C hD1 ha2 (hK₀S hsK) (hK₀a s hsK) (hK₀2 s hsK) hF
          (Or.inr (by rw [hsσ]; exact h))
      · exact hzP (by
          have : (σ' : Perm (Fin 5)) = zA := h
          rw [← this]; exact σ'.2)
    · have h1 := GMate.card_KQ_le (m := m) C hK₀S hK₀a hK₀ab
      have h2 : Nat.card ↥(C.U ⊓ conjR (C.U) a ⊓
          Subgroup.centralizer (K₀ : Set G)) ≤
          Nat.card ↥(C.U ⊓ conjR (C.U) a ⊓ Subgroup.centralizer ({s} : Set G)) :=
        Subgroup.card_le_of_le (inf_le_inf_left _ (Subgroup.centralizer_le
          (Set.singleton_subset_iff.2 hsK)))
      have h3 := GMate.card_F_cent_le_two (m := m) C (hK₀S hsK) (by rw [hsσ]; exact hσE)
      omega
  ·
    omega

end GMate

theorem isMaxElemAbelian_M₀_iff {T M H S L : Subgroup G} (C : GCfg T M H S L)
    {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2)
    (A' : Subgroup G) : IsMaxElemAbelian M₀ A' ↔ IsMaxElemAbelian S A' := by
  have hne : S ≠ M₀ := fun h => by
    rw [← h] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  have m₀ : GMate S T M₀ x₀ := ⟨hSM, hMT, h2, hx₀, hx₀S⟩
  have hlt : ∀ A' : Subgroup G, IsElemAbelian 2 A' → A' ≤ M₀ → ¬ A' ≤ S →
      Nat.card ↥A' < Nat.card ↥(pCoreOf 2 H) := by
    intro A' hA' hA'M hA'S
    obtain ⟨a, haA, haS⟩ : ∃ a ∈ A', a ∉ S := by
      by_contra hcon
      push Not at hcon
      exact hA'S hcon
    have ma : GMate S T M₀ a := ⟨hSM, hMT, h2, hA'M haA, haS⟩
    exact GMate.card_lt_Q (m := ma) C hA' hA'M haA
  have hQmax := GMate.Q_isMax (m := m₀) C
  constructor
  · rintro ⟨hA'M, hA'e, hA'max⟩
    have hQle : Nat.card ↥(pCoreOf 2 H) ≤ Nat.card ↥A' :=
      hA'max _ (C.hQS.trans hSM) hQmax.2.1
    have hA'S : A' ≤ S := by
      by_contra hcon
      exact absurd (hlt A' hA'e hA'M hcon) (not_lt.2 hQle)
    exact ⟨hA'S, hA'e, fun B hBS hBe => hA'max B (hBS.trans hSM) hBe⟩
  · intro hA'
    refine ⟨hA'.1.trans hSM, hA'.2.1, fun B hBM hBe => ?_⟩
    by_cases hBS : B ≤ S
    · exact hA'.2.2 B hBS hBe
    · exact (hlt B hBe hBM hBS).le.trans (GMate.card_eq_Q (m := m₀) C hA').ge

theorem thompsonJ_M₀_eq {T M H S L : Subgroup G} (C : GCfg T M H S L)
    {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) :
    thompsonJ M₀ = thompsonJ S := by
  unfold CFSG.Quasithin.thompsonJ
  refine iSup_congr fun A' => ?_
  exact iSup_congr_Prop (isMaxElemAbelian_M₀_iff C hSM hMT h2 A') fun _ => rfl

end CFSG.QuasithinUnique.burnsideC56_P.AppD
