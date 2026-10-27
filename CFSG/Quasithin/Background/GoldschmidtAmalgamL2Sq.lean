module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2Centre
public import CFSG.Quasithin.Recognition.F112TitsB2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem GoldHyp.eq_one_of_centralizes (h : GoldHyp G₁ G₂) {ε : D} (hεT : ε ∈ G₁ ⊓ G₂)
    (h₁ : ∀ g ∈ G₁, g * ε = ε * g) (h₂ : ∀ g ∈ G₂, g * ε = ε * g) : ε = 1 := by
  have hN : Subgroup.zpowers ε ≤ ⊥ := by
    refine le_of_eq (h.eq_bot_of_normalizes ?_ ?_ ?_)
    · intro g hg
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact ((show Commute g ε from h₁ g hg).zpow_right k).symm.eq
    · intro g hg
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact ((show Commute g ε from h₂ g hg).zpow_right k).symm.eq
    · exact Subgroup.zpowers_le.mpr hεT
  exact Subgroup.mem_bot.mp (hN (Subgroup.mem_zpowers ε))

theorem omega_labelling_iff (h : GoldHyp G₁ G₂) (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂)) {z : D}
    {V : Subgroup D} (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V)
    (hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2) :
    ((∀ ω ∈ centerOf (G₁ ⊓ G₂), ω ^ 2 = 1 → ∀ y ∈ G₂, y * ω * y⁻¹ = ω) ↔
      (∀ ε ∈ centerOf (G₁ ⊓ G₂), ε * ε = 1 → (∀ y ∈ G₁, y * ε = ε * y) → ε = 1)) ∧
    ((∀ ε ∈ centerOf (G₁ ⊓ G₂), ε * ε = 1 → (∀ y ∈ G₁, y * ε = ε * y) → ε = 1) ↔
      (∀ ω ∈ centerOf (G₁ ⊓ G₂), ω ^ 2 = 1 → ω = 1 ∨ ω = z)) := by
  have hzG₂ := centralizes_of_critDist_two h hn hb
  refine ⟨⟨fun hG₂ ε hεZ hε2 hε₁ => ?_, fun hA ω hωZ hω2 y hy => ?_⟩,
    ⟨fun hA ω hωZ hω2 => eq_one_or_eq_of_trivial_central h h32 hn hb hA hωZ hω2,
      fun hU ε hεZ hε2 hε₁ => ?_⟩⟩
  ·
    exact h.eq_one_of_centralizes hεZ.1 hε₁ fun y hy =>
      mul_eq_of_conj_eq (hG₂ ε hεZ (by rw [pow_two]; exact hε2) y hy)
  ·
    rcases eq_one_or_eq_of_trivial_central h h32 hn hb hA hωZ hω2 with h1 | h1
    · rw [h1]; group
    · rw [h1]; exact hzG₂ y hy
  ·
    rcases hU ε hεZ (by rw [pow_two]; exact hε2) with h1 | h1
    · exact h1
    · exfalso
      apply hn.not_normalizes
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hc : g * z = z * g := by rw [← h1]; exact hε₁ g hg
      exact ((show Commute g z from hc).zpow_right k).symm.eq

theorem sq_mem_of_conjClosure (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) (hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2) {x : D}
    (hx : x ∈ conjClosure V G₂) : x * x ∈ Subgroup.zpowers z := by
  have hzG₂ := centralizes_of_critDist_two h hn hb
  have hUU := (two_structure_of_critDist_two h hn hb).2.2.2
  have hUQ : conjClosure V G₂ ≤ pCoreOf 2 G₂ := (critDist_two_structure_of_natural h hn hb).2.1
  have hzc : ∀ g ∈ G₂, ∀ y ∈ Subgroup.zpowers z, g * y = y * g := by
    intro g hg y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute g z from mul_eq_of_conj_eq (hzG₂ g hg)).zpow_right k).eq
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, v, hv, rfl⟩ := hx
    have h1 : v * v = 1 := hn.mul_self_of_mem hv
    have e : g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
    rw [e, h1]
    simp
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hx' : x ∈ conjClosure V G₂ := hx
    have hy' : y ∈ conjClosure V G₂ := hy
    have hxG : x ∈ G₂ := pCoreOf_le 2 G₂ (hUQ hx')
    have hc : y * x * y⁻¹ * x⁻¹ ∈ Subgroup.zpowers z := by
      have := Subgroup.commutator_mem_commutator hy' hx'
      rw [hUU] at this
      exact this
    have hxc : x * (y * x * y⁻¹ * x⁻¹) = (y * x * y⁻¹ * x⁻¹) * x := hzc x hxG _ hc
    have e : x * y * (x * y) = (y * x * y⁻¹ * x⁻¹) * (x * x) * (y * y) := by
      calc x * y * (x * y) = x * (y * x * y⁻¹ * x⁻¹) * x * y * y := by group
        _ = (y * x * y⁻¹ * x⁻¹) * x * x * y * y := by rw [hxc]
        _ = (y * x * y⁻¹ * x⁻¹) * (x * x) * (y * y) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc ihx) ihy
  | inv x hx ih =>
    have e : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ih

omit [Finite D] in
theorem card_map_eq_relIndex_ker' {L N : Type*} [Group L] [Group N] (φ : L →* N)
    (A : Subgroup L) : Nat.card (A.map φ) = φ.ker.relIndex A := by
  let ψ : ↥A →* N := φ.comp A.subtype
  have h1 : ψ.range = A.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h2 : ψ.ker = φ.ker.subgroupOf A := (MonoidHom.comap_ker φ A.subtype).symm
  rw [← h1, Subgroup.relIndex, ← h2, Subgroup.index_ker]

theorem b2Hyp_of_critDist_two (h : GoldHyp G₁ G₂) (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂)) {z : D}
    {V : Subgroup D} (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V)
    (hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2)
    (hA : ∀ ε ∈ centerOf (G₁ ⊓ G₂), ε * ε = 1 → (∀ y ∈ G₁, y * ε = ε * y) → ε = 1)
    {φ : ↥G₁ →* Equiv.Perm (Fin 3)} (hφ : ∀ x : ↥G₁, φ x = 1 ↔ (x : D) ∈ pCoreOf 2 G₁) :
    F112T.B2Hyp φ ((G₁ ⊓ G₂).subgroupOf G₁) ((pCoreOf 2 G₂).subgroupOf G₁)
      ((conjClosure V G₂).subgroupOf G₁) (V.subgroupOf G₁)
      ((Subgroup.zpowers z).subgroupOf G₁) := by
  have hVG₁ : V ≤ G₁ := hn.reduced.1
  have hUQ : conjClosure V G₂ ≤ pCoreOf 2 G₂ := (critDist_two_structure_of_natural h hn hb).2.1
  have hUQc := (two_structure_of_critDist_two h hn hb).2.2.1
  refine
    { hT2 := h.amalgam.toIsGoldschmidtVTriple.isPGroup_inf.of_equiv
        (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
      hRT := ?_
      hπT := ?_
      hQT := fun x hx => Subgroup.mem_subgroupOf.mpr
        (h.pCoreOf_right_le (Subgroup.mem_subgroupOf.mp hx))
      hUQ := fun x hx => Subgroup.mem_subgroupOf.mpr (hUQ (Subgroup.mem_subgroupOf.mp hx))
      hVU := fun x hx => Subgroup.mem_subgroupOf.mpr
        (le_conjClosure V G₂ (Subgroup.mem_subgroupOf.mp hx))
      hZV := fun x hx => Subgroup.mem_subgroupOf.mpr
        (Subgroup.zpowers_le.mpr hn.z_mem_V (Subgroup.mem_subgroupOf.mp hx))
      hTQ := ?_
      hTU := ?_
      hVn := ?_
      hVsq := ?_
      hV4 := ?_
      hRV := ?_
      hCV := ?_
      hVmin := ?_
      hUsq := ?_
      hUQ' := ?_
      hCyc := ?_ }
  · intro x hx
    have hx' : (x : D) ∈ pCoreOf 2 G₁ := (hφ x).mp (MonoidHom.mem_ker.mp hx)
    exact Subgroup.mem_subgroupOf.mpr (h.pCoreOf_left_le hx')
  · rw [card_map_eq_relIndex_ker']
    have hker : φ.ker = (pCoreOf 2 G₁).subgroupOf G₁ := by
      ext x
      rw [MonoidHom.mem_ker, hφ, Subgroup.mem_subgroupOf]
    rw [hker, Subgroup.relIndex_subgroupOf inf_le_left]
    exact h.relIndex_pCoreOf_T_left
  · intro t ht q hq
    rw [Subgroup.mem_subgroupOf] at ht hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂ ht.2) (q : D)).mp hq
  · intro t ht x hx
    rw [Subgroup.mem_subgroupOf] at ht hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V G₂ ht.2) (x : D)).mp hx
  · intro l v hv
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hn.reduced.2.1 l.2) (v : D)).mp hv
  · intro v hv
    exact Subtype.ext (hn.mul_self_of_mem (Subgroup.mem_subgroupOf.mp hv))
  · rw [← hn.card_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVG₁).toEquiv
  · intro r hr v hv
    have hr' : (r : D) ∈ pCoreOf 2 G₁ := (hφ r).mp (MonoidHom.mem_ker.mp hr)
    have := Subgroup.mem_centralizer_iff.mp (hn.le_center (Subgroup.mem_subgroupOf.mp hv)).2
      (r : D) hr'
    exact Subtype.ext this
  · intro l hl
    rw [MonoidHom.mem_ker, hφ]
    have hlc : (l : D) ∈ G₁ ⊓ Subgroup.centralizer (V : Set D) := by
      refine ⟨l.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have := hl ⟨v, hVG₁ hv⟩ (Subgroup.mem_subgroupOf.mpr hv)
      exact (congrArg Subtype.val this).symm
    rw [hn.centralizer_eq] at hlc
    exact hlc
  · intro N hNT hN1 hNn
    have hN'T : N.map G₁.subtype ≤ G₁ ⊓ G₂ := by
      rintro _ ⟨n, hn', rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hNT hn')
    have hN'1 : N.map G₁.subtype ≠ ⊥ := by
      intro hbot
      apply hN1
      rw [eq_bot_iff]
      intro n hn'
      have : (n : D) ∈ N.map G₁.subtype := ⟨n, hn', rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    have hN'n : ∀ l ∈ G₁, ∀ m ∈ N.map G₁.subtype, l * m * l⁻¹ ∈ N.map G₁.subtype := by
      rintro l hl _ ⟨n, hn', rfl⟩
      exact ⟨⟨l, hl⟩ * n * ⟨l, hl⟩⁻¹, hNn _ n hn', rfl⟩
    have hVN := V_le_of_normal h h32 hn hb hA hN'T hN'1 hN'n
    intro v hv
    obtain ⟨n, hn', hnv⟩ := hVN (Subgroup.mem_subgroupOf.mp hv)
    have : n = v := Subtype.ext hnv
    rwa [← this]
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (sq_mem_of_conjClosure h hn hb (Subgroup.mem_subgroupOf.mp hx))
  · intro x hx q hq
    exact Subgroup.mem_subgroupOf.mpr (hUQc.le (Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hq)))
  · intro X hXT _
    have h2 : ((pCoreOf 2 G₂).subgroupOf G₁).relIndex ((G₁ ⊓ G₂).subgroupOf G₁) = 2 := by
      rw [Subgroup.relIndex_subgroupOf inf_le_left]
      exact h.relIndex_pCoreOf_T_right
    rw [Subgroup.inf_relIndex_right]
    calc ((pCoreOf 2 G₂).subgroupOf G₁).relIndex X
        ≤ ((pCoreOf 2 G₂).subgroupOf G₁).relIndex ((G₁ ⊓ G₂).subgroupOf G₁) :=
          Subgroup.relIndex_le_of_le_right hXT (by rw [h2]; norm_num)
      _ = 2 := h2

theorem sq_mem_pCoreOf_of_critDist_two (h : GoldHyp G₁ G₂) (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂))
    {z : D} {V : Subgroup D} (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V)
    (hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2)
    (hA : ∀ ε ∈ centerOf (G₁ ⊓ G₂), ε * ε = 1 → (∀ y ∈ G₁, y * ε = ε * y) → ε = 1) :
    ∀ r ∈ pCoreOf 2 G₁, r * r ∈ pCoreOf 2 G₂ := by
  obtain ⟨φ, hφs, hφ⟩ := h.vertex_left.exists_hom
  have H := b2Hyp_of_critDist_two h h32 hn hb hA hφ
  obtain ⟨-, -, -, x, hxG₂, hWU, hWG, hQW, -, -, -, -, -⟩ :=
    critDist_two_structure_of_natural h hn hb
  obtain ⟨w, hwW, hwQ⟩ : ∃ w ∈ conjSub x V, w ∉ pCoreOf 2 G₁ := by
    by_contra hcon
    push Not at hcon
    have hle : conjSub x V ≤ pCoreOf 2 G₁ := fun w hw => hcon w hw
    rw [sup_eq_left.mpr hle] at hQW
    have h1 := h.relIndex_pCoreOf_T_left
    rw [hQW, Subgroup.relIndex_self] at h1
    omega
  have hw2 : w * w = 1 := by
    have hv := mem_conjSub.mp hwW
    have h1 := hn.mul_self_of_mem hv
    have e : w * w = x * ((x⁻¹ * w * x) * (x⁻¹ * w * x)) * x⁻¹ := by group
    rw [e, h1]
    group
  intro r hr
  have hu1 : φ ⟨w, hWG hwW⟩ ≠ 1 := fun h1 => hwQ ((hφ _).mp h1)
  have := H.sq_mem_Q hφs (u := ⟨w, hWG hwW⟩) (Subgroup.mem_subgroupOf.mpr (hWU hwW))
    (Subtype.ext hw2) hu1 (r := ⟨r, pCoreOf_le 2 G₁ hr⟩) ((hφ _).mpr hr)
  exact Subgroup.mem_subgroupOf.mp this

end GoldAmL

end F6

end CFSG.Quasithin
