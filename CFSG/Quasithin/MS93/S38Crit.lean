module

public import CFSG.Quasithin.MS93.Sec2Three

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ SimpleGraph
open scoped commutatorElement

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem commutator_sup_eq_of_le_centralizer {G : Type*} [Group G] {X K Q : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (X : Set G)) (hQ : Q ≤ Subgroup.centralizer (X : Set G)) :
    ⁅X, K ⊔ Q⁆ = ⁅X, K⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono le_rfl le_sup_left)
  have hXK : ⁅X, K⁆ ≤ X := Subgroup.le_normalizer_iff_commutator_le_left.mp hK
  have hKn : K ≤ Subgroup.normalizer ((⁅X, K⁆ : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have key : ∀ k ∈ K, ∀ y ∈ ⁅X, K⁆, k * y * k⁻¹ ∈ ⁅X, K⁆ := by
      intro k hk y hy
      have hle : ⁅X, K⁆ ≤ ⁅X, K⁆.comap (MulAut.conj k).toMonoidHom := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        show (MulAut.conj k) ⁅a, b⁆ ∈ ⁅X, K⁆
        rw [map_commutatorElement]
        exact Subgroup.commutator_mem_commutator
          ((Subgroup.mem_normalizer_iff.mp (hK hk) a).mp ha) (K.mul_mem (K.mul_mem hk hb)
            (K.inv_mem hk))
      exact hle hy
    refine ⟨key k hk y, fun hy => ?_⟩
    have := key k⁻¹ (K.inv_mem hk) _ hy
    simpa [mul_assoc] using this
  let H : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer ((⁅X, K⁆ : Subgroup G) : Set G) ∧
        ∀ x ∈ X, ⁅x, g⁆ ∈ ⁅X, K⁆}
      one_mem' := ⟨Subgroup.one_mem _, fun x _ => by simp⟩
      mul_mem' := by
        rintro g k ⟨hg, hg'⟩ ⟨hk, hk'⟩
        refine ⟨Subgroup.mul_mem _ hg hk, fun x hx => ?_⟩
        have e : ⁅x, g * k⁆ = ⁅x, g⁆ * (g * ⁅x, k⁆ * g⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ (hg' x hx)
          ((Subgroup.mem_normalizer_iff.mp hg _).mp (hk' x hx))
      inv_mem' := by
        rintro g ⟨hg, hg'⟩
        refine ⟨Subgroup.inv_mem _ hg, fun x hx => ?_⟩
        have e : ⁅x, g⁻¹⁆ = g⁻¹ * ⁅x, g⁆⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp
          (Subgroup.inv_mem _ (hg' x hx)) }
  have hKH : K ≤ H := fun k hk => ⟨hKn hk, fun x hx => Subgroup.commutator_mem_commutator hx hk⟩
  have hQH : Q ≤ H := by
    intro q hq
    have hc : ∀ x ∈ X, ⁅x, q⁆ = 1 := by
      intro x hx
      have := Subgroup.mem_centralizer_iff.mp (hQ hq) x hx
      simp only [commutatorElement_def]
      rw [this]
      group
    refine ⟨?_, fun x hx => by rw [hc x hx]; exact Subgroup.one_mem _⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hy : ∀ y ∈ ⁅X, K⁆, q * y * q⁻¹ = y := by
      intro y hy
      have := Subgroup.mem_centralizer_iff.mp (hQ hq) y (hXK hy)
      rw [← this]
      group
    constructor
    · intro h'
      rw [hy y h']
      exact h'
    · intro h'
      have e : y = q⁻¹ * (q * y * q⁻¹) * q := by group
      have h2 : q * y * q⁻¹ ∈ X := hXK h'
      have h3 := Subgroup.mem_centralizer_iff.mp (hQ (Q.inv_mem hq)) _ h2
      rw [e, ← h3]
      simpa [mul_assoc] using h'
  rw [Subgroup.commutator_le]
  intro x hx g hg
  exact (sup_le hKH hQH hg).2 x hx

@[expose] def IsOffAt (γ ρ : Vtx X) (F : Subgroup X.Universal) : Prop :=
  F ≤ Qv X ρ ∧ CFSG.Open.IsElemAbelian 2 F ∧ ¬ F ≤ Qv X γ ∧
    (Subgroup.centralizer (F : Set X.Universal)).relIndex (XM X γ) ≤ (Qv X γ).relIndex F

structure OffDataAt (γ ρ : Vtx X) : Prop where
  uniq : ∀ F₁ F₂ : Subgroup X.Universal, IsOffAt X γ ρ F₁ → IsOffAt X γ ρ F₂ →
    F₁ ⊔ Qv X γ = F₂ ⊔ Qv X γ
  eq : ∀ F : Subgroup X.Universal, IsOffAt X γ ρ F →
    (Subgroup.centralizer (F : Set X.Universal)).relIndex (XM X γ) = (Qv X γ).relIndex F
  zc : ∀ F : Subgroup X.Universal, IsOffAt X γ ρ F → ∃ Z : Subgroup X.Universal, Z ≤ XM X γ ∧
    ¬ Z ≤ Subgroup.centralizer (F : Set X.Universal) ∧
    ∀ Y : Subgroup X.Universal, Y ≤ Qv X ρ → Y ≤ Subgroup.centralizer (F : Set X.Universal) →
      ⁅Y, Z⁆ ≤ ⁅XM X γ, F⁆ ⊔ ⁅Y, XM X γ ⊓ Subgroup.centralizer (F : Set X.Universal)⁆

theorem isOffAt_smul {γ ρ : Vtx X} {F : Subgroup X.Universal} (hF : IsOffAt X γ ρ F)
    (g : X.Universal) : IsOffAt X (g • γ) (g • ρ) (F.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hFρ, hF, hFγ, hineq⟩ := hF
  refine ⟨?_, (isElemAbelian_map_mulEquiv _).mpr hF, ?_, ?_⟩
  · rw [qv_smul]
    exact Subgroup.map_mono hFρ
  · rwa [qv_smul, map_conj_le_map_conj_iff]
  · rw [← centralizer_map_mulEquiv, xm_smul, qv_smul,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hineq

theorem isOffAt_smul_iff {γ ρ : Vtx X} {F : Subgroup X.Universal} (g : X.Universal) :
    IsOffAt X (g • γ) (g • ρ) F ↔ IsOffAt X γ ρ (F.map (MulAut.conj g⁻¹).toMonoidHom) := by
  constructor
  · intro hF
    have := isOffAt_smul X hF g⁻¹
    rwa [inv_smul_smul, inv_smul_smul] at this
  · intro hF
    have := isOffAt_smul X hF g
    rwa [map_conj_map_conj, mul_inv_cancel, map_conj_one] at this

theorem OffDataAt.smul {γ ρ : Vtx X} (hO : OffDataAt X γ ρ) (g : X.Universal) :
    OffDataAt X (g • γ) (g • ρ) := by
  have back : ∀ K : Subgroup X.Universal,
      (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := fun K => by
    rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]
  refine ⟨fun F₁ F₂ h₁ h₂ => ?_, fun F hF => ?_, fun F hF => ?_⟩
  · have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom)
      (hO.uniq _ _ ((isOffAt_smul_iff X g).mp h₁) ((isOffAt_smul_iff X g).mp h₂))
    rwa [Subgroup.map_sup, Subgroup.map_sup, back, back, ← qv_smul] at this
  · have h := hO.eq _ ((isOffAt_smul_iff X g).mp hF)
    rw [← back F, ← centralizer_map_mulEquiv, xm_smul, qv_smul,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact h
  · obtain ⟨Z, hZX, hZF, hY⟩ := hO.zc _ ((isOffAt_smul_iff X g).mp hF)
    refine ⟨Z.map (MulAut.conj g).toMonoidHom, ?_, ?_, fun Y hYρ hYF => ?_⟩
    · rw [xm_smul]
      exact Subgroup.map_mono hZX
    · rwa [← back F, ← centralizer_map_mulEquiv, map_conj_le_map_conj_iff]
    · have hYρ' : Y.map (MulAut.conj g⁻¹).toMonoidHom ≤ Qv X ρ := by
        rw [qv_smul] at hYρ
        rw [← map_conj_le_map_conj_iff g, back]
        exact hYρ
      have hYF' : Y.map (MulAut.conj g⁻¹).toMonoidHom ≤
          Subgroup.centralizer ((F.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup _) :
            Set X.Universal) := by
        rw [← centralizer_map_mulEquiv]
        exact Subgroup.map_mono hYF
      have key := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (hY _ hYρ' hYF')
      rw [Subgroup.map_commutator, back, Subgroup.map_sup, Subgroup.map_commutator,
        Subgroup.map_commutator, back, back, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
        ← xm_smul, centralizer_map_mulEquiv, back] at key
      exact key

theorem offDataAt_of_edge {α β : Vtx X} (hα : IsMVtx X α) (hαβ : X.treeGraph.Adj α β)
    (hO : OffDataAt X α β) {γ ρ : Vtx X} (hγ : IsMVtx X γ) (hγρ : X.treeGraph.Adj γ ρ) :
    OffDataAt X γ ρ := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx X hα hαβ hγ hγρ
  exact hO.smul X g

variable {X}

private theorem relIndex_ne_zero_of_le' {H K P : Subgroup X.Universal} (hKP : K ≤ P)
    [Finite P] : H.relIndex K ≠ 0 := by
  have : Finite K := Finite.of_injective _ (Subgroup.inclusion_injective hKP)
  exact Subgroup.index_ne_zero_of_finite

private theorem relIndex_centralizer_le' {Q V E P : Subgroup X.Universal} (hEP : E ≤ P)
    [Finite P] (hQV : Q ≤ Subgroup.centralizer (V : Set X.Universal)) :
    (Subgroup.centralizer (V : Set X.Universal)).relIndex E ≤ Q.relIndex E := by
  rw [← Subgroup.inf_relIndex_right, ← Subgroup.inf_relIndex_right (H := Q)]
  exact Subgroup.relIndex_le_of_le_left (inf_le_inf_right _ hQV)
    (relIndex_ne_zero_of_le' hEP)

variable (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X)
include h hb hC

theorem xm_not_le_qv_of_isCritical {α α' : Vtx X} (hc : IsCritical X α α') :
    ¬ XM X α' ≤ Qv X α := fun hle =>
  (ms22_iii X h hb hC hc).2.2 ((zm_le_xm X h hb (hc.isMVtx_right X h)).trans hle)

theorem isOffAt_xm {α α' : Vtx X} (hc : IsCritical X α α')
    (hO : OffDataAt X α (geo X α α' 1)) (hO' : OffDataAt X α' (geo X α' α 1)) :
    IsOffAt X α (geo X α α' 1) (XM X α') ∧ IsOffAt X α' (geo X α' α 1) (XM X α) := by
  have hc' := ms22_iii X h hb hC hc
  have hα := hc.1
  have hα' := hc.isMVtx_right X h
  set β := geo X α α' 1
  set γ := geo X α' α 1
  have hαβ : X.treeGraph.Adj α β := adj_geo_one_of_isCritical X hb hc
  have hα'γ : X.treeGraph.Adj α' γ := adj_geo_one_of_isCritical X hb hc'
  have : Finite (Qv X β) := finite_qv X h ((isMVtx_iff_of_adj X hαβ).mp hα)
  have : Finite (Qv X γ) := finite_qv X h ((isMVtx_iff_of_adj X hα'γ).mp hα')
  have hXβ : XM X α' ≤ Qv X β := xm_le_qv_geo_one X h hb hC hc
  have hXγ : XM X α ≤ Qv X γ := xm_le_qv_geo_one X h hb hC hc'
  have hn : ¬ XM X α' ≤ Qv X α := xm_not_le_qv_of_isCritical h hb hC hc
  have hn' : ¬ XM X α ≤ Qv X α' := xm_not_le_qv_of_isCritical h hb hC hc'
  have hca : (Subgroup.centralizer (XM X α' : Set X.Universal)).relIndex (XM X α) ≤
      (Qv X α').relIndex (XM X α) := relIndex_centralizer_le' hXγ (qv_le_centralizer_xm X α')
  have hca' : (Subgroup.centralizer (XM X α : Set X.Universal)).relIndex (XM X α') ≤
      (Qv X α).relIndex (XM X α') := relIndex_centralizer_le' hXβ (qv_le_centralizer_xm X α)
  rcases le_or_gt ((Qv X α').relIndex (XM X α)) ((Qv X α).relIndex (XM X α')) with hle | hlt
  · have h1 : IsOffAt X α β (XM X α') :=
      ⟨hXβ, isElemAbelian_xm X α', hn, hca.trans hle⟩
    have he := hO.eq _ h1
    refine ⟨h1, hXγ, isElemAbelian_xm X α, hn', ?_⟩
    omega
  · exfalso
    have h1 : IsOffAt X α' γ (XM X α) :=
      ⟨hXγ, isElemAbelian_xm X α, hn', hca'.trans hlt.le⟩
    have he := hO'.eq _ h1
    omega

theorem xm_inf_centralizer_eq {α α' : Vtx X} (hc : IsCritical X α α') :
    XM X α' ⊓ Subgroup.centralizer (XM X α : Set X.Universal) = XM X α' ⊓ Qv X α := by
  refine le_antisymm (le_inf inf_le_left ?_) (inf_le_inf_left _ (qv_le_centralizer_xm X α))
  have hαβ := adj_geo_one_of_isCritical X hb hc
  refine le_qv_of_le_centralizer X hC hc.1 hαβ
    (inf_le_left.trans (xm_le_qv_geo_one X h hb hC hc)) ?_
  exact inf_le_right.trans (Subgroup.centralizer_le (zm_le_xm X h hb hc.1))

theorem zc23At_of_offData {α α' : Vtx X} (hc : IsCritical X α α')
    (hO : OffDataAt X α (geo X α α' 1)) (hO' : OffDataAt X α' (geo X α' α 1)) :
    ∃ Z : Subgroup X.Universal, Z ≤ XM X α' ∧ ¬ Z ≤ Qv X α ∧
      ∀ Y : Subgroup X.Universal, Y ≤ Qv X (geo X α' α 1) →
        CFSG.Open.IsElemAbelian 2 (Y ⊔ XM X α) →
          ⁅Y, Z⁆ ≤ ⁅XM X α, XM X α'⁆ ⊔ ⁅Y, XM X α' ⊓ Qv X α⁆ := by
  have hoff := (isOffAt_xm h hb hC hc hO hO').2
  obtain ⟨Z, hZX, hZF, hY⟩ := hO'.zc _ hoff
  refine ⟨Z, hZX, fun hZQ => hZF (hZQ.trans (qv_le_centralizer_xm X α)), fun Y hYρ hYe => ?_⟩
  have hYF : Y ≤ Subgroup.centralizer (XM X α : Set X.Universal) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hYe.1.1.1 ⟨x, Subgroup.mem_sup_right hx⟩ ⟨y, Subgroup.mem_sup_left hy⟩
    exact congrArg Subtype.val this
  have key := hY Y hYρ hYF
  rwa [Subgroup.commutator_comm (XM X α'), xm_inf_centralizer_eq h hb hC hc] at key

omit h hb hC in
theorem mem_normalizer_of_map_conj_eq {K : Subgroup X.Universal} {t : X.Universal}
    (ht : K.map (MulAut.conj t).toMonoidHom = K) :
    t ∈ Subgroup.normalizer (K : Set X.Universal) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← ht]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← ht] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      have := (MulAut.conj t).injective (a₁ := z) (a₂ := y)
      exact this (by simpa using hzy)
    rwa [← this]

theorem commutator_xm_eq
    (hO : ∀ γ ρ : Vtx X, IsMVtx X γ → X.treeGraph.Adj γ ρ → OffDataAt X γ ρ)
    {α α' δ' : Vtx X} (hc : IsCritical X α α') (hd : IsCritical X α δ')
    (hgeo : geo X α δ' 1 = geo X α α' 1) : ⁅XM X α, XM X α'⁆ = ⁅XM X α, XM X δ'⁆ := by
  have hc' := ms22_iii X h hb hC hc
  have hd' := ms22_iii X h hb hC hd
  set β := geo X α α' 1
  have hαβ : X.treeGraph.Adj α β := adj_geo_one_of_isCritical X hb hc
  have h1 := (isOffAt_xm h hb hC hc (hO _ _ hc.1 hαβ)
    (hO _ _ (hc.isMVtx_right X h) (adj_geo_one_of_isCritical X hb hc'))).1
  have h2 := (isOffAt_xm h hb hC hd (hO _ _ hd.1 (adj_geo_one_of_isCritical X hb hd))
    (hO _ _ (hd.isMVtx_right X h) (adj_geo_one_of_isCritical X hb hd'))).1
  rw [hgeo] at h2
  have hu := (hO _ _ hc.1 hαβ).uniq _ _ h1 h2
  have hn : ∀ {δ : Vtx X}, IsCritical X α δ →
      XM X δ ≤ Subgroup.normalizer (XM X α : Set X.Universal) := fun hδ =>
    (xm_le_qv_geo_one X h hb hC hδ).trans ((qv_le_stab_of_adj X
      (adj_geo_one_of_isCritical X hb hδ).symm).trans (stab_le_normalizer_xm X α))
  rw [← commutator_sup_eq_of_le_centralizer (hn hc) (qv_le_centralizer_xm X α),
    ← commutator_sup_eq_of_le_centralizer (hn hd) (qv_le_centralizer_xm X α), hu]

theorem normalizer_commutator_xm
    (hO : ∀ γ ρ : Vtx X, IsMVtx X γ → X.treeGraph.Adj γ ρ → OffDataAt X γ ρ)
    {α α' : Vtx X} (hc : IsCritical X α α') :
    Qv X (geo X α α' 1) ≤ Subgroup.normalizer ((⁅XM X α, XM X α'⁆ : Subgroup X.Universal) :
      Set X.Universal) := by
  intro t ht
  have hαβ : X.treeGraph.Adj α (geo X α α' 1) := adj_geo_one_of_isCritical X hb hc
  have htα : t • α = α := (mem_stab X).mp (qv_le_stab_of_adj X hαβ.symm ht)
  have htβ : t • geo X α α' 1 = geo X α α' 1 := (mem_stab X).mp (qv_le_stab X _ ht)
  have hct : IsCritical X α (t • α') := by
    have := (isCritical_smul X t α α').mpr hc
    rwa [htα] at this
  have hgeo : geo X α (t • α') 1 = geo X α α' 1 := by
    conv_lhs => rw [← htα]
    rw [geo_smul, htβ]
  refine mem_normalizer_of_map_conj_eq ?_
  rw [Subgroup.map_commutator, ← xm_smul, ← xm_smul, htα]
  exact (commutator_xm_eq h hb hC hO hc hct hgeo).symm

theorem ms23_of_offData (ha : 2 < critDist X)
    (hG : ∀ γ ρ : Vtx X, IsMVtx X γ → X.treeGraph.Adj γ ρ → Gen23At X γ ρ)
    (hO : ∀ γ ρ : Vtx X, IsMVtx X γ → X.treeGraph.Adj γ ρ → OffDataAt X γ ρ)
    (hN : ∀ ε ε' : Vtx X, IsCritical X ε ε' →
      ¬ stab X ε ≤ Subgroup.normalizer ((⁅XM X ε, XM X ε'⁆ : Subgroup X.Universal) :
        Set X.Universal)) :
    critDist X = 4 ∧ ∀ ε ε' : Vtx X, IsCritical X ε ε' →
      stab X (geo X ε ε' 2) ≤ Subgroup.normalizer ((⁅XM X ε, XM X ε'⁆ : Subgroup X.Universal) :
        Set X.Universal) := by
  have key : ∀ ε ε' : Vtx X, IsCritical X ε ε' → critDist X = 4 ∧
      stab X (geo X ε ε' 2) ≤ Subgroup.normalizer ((⁅XM X ε, XM X ε'⁆ : Subgroup X.Universal) :
        Set X.Universal) := by
    intro ε ε' hc
    have hεβ := adj_geo_one_of_isCritical X hb hc
    have := ms23 X h hc.1 hεβ ha (hG _ _ hc.1 hεβ)
      (fun α' hc' hgeo => by
        have hc'' := ms22_iii X h hb hC hc'
        exact zc23At_of_offData h hb hC hc'
          (hO _ _ hc'.1 (adj_geo_one_of_isCritical X hb hc'))
          (hO _ _ (hc'.isMVtx_right X h) (adj_geo_one_of_isCritical X hb hc'')))
      (normalizer_commutator_xm h hb hC hO hc) (hN ε ε' hc)
      (fun δ' hd hgeo => (commutator_xm_eq h hb hC hO hc hd hgeo).le)
    exact ⟨this.1, this.2 ε' hc rfl⟩
  obtain ⟨α, α', hc⟩ := exists_isCritical X h
  exact ⟨(key α α' hc).1, fun ε ε' hc => (key ε ε' hc).2⟩

end CFSG.Quasithin.MS93
