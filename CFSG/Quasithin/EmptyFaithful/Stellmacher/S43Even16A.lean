module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace C16

variable {G : Type} [Group G] {H M S : Subgroup G}

theorem conjSub_fixSecIn (g : G) (A L N : Subgroup G) :
    conjSub g (fixSecIn A L N) = fixSecIn (conjSub g A) (conjSub g L) (conjSub g N) := by
  unfold fixSecIn
  rw [conjSub_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxa⟩, rfl⟩
    refine ⟨mul_mem_conjSub hx, fun a' ha' => ?_⟩
    have ha := mem_conjSub.mp ha'
    have h1 := mul_mem_conjSub (g := g) (hxa _ ha)
    have e : g * (g⁻¹ * a' * g * x * (g⁻¹ * a' * g)⁻¹ * x⁻¹) * g⁻¹ =
        a' * (g * x * g⁻¹) * a'⁻¹ * (g * x * g⁻¹)⁻¹ := by group
    rwa [e] at h1
  · rintro ⟨hy, hya⟩
    refine ⟨g⁻¹ * y * g, ⟨mem_conjSub.mp hy, fun a ha => ?_⟩, by group⟩
    have h1 := mem_conjSub.mp (hya (g * a * g⁻¹) (mul_mem_conjSub ha))
    have e : g⁻¹ * (g * a * g⁻¹ * y * (g * a * g⁻¹)⁻¹ * y⁻¹) * g =
        a * (g⁻¹ * y * g) * a⁻¹ * (g⁻¹ * y * g)⁻¹ := by group
    rwa [e] at h1

theorem secIdx_conjSub (g : G) (A L N : Subgroup G) :
    secIdx (conjSub g A) (conjSub g L) (conjSub g N) = secIdx A L N := by
  unfold secIdx
  rw [← conjSub_fixSecIn]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

theorem conjSub_zpowers (g x : G) :
    conjSub g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) :=
  MonoidHom.map_zpowers _ x

theorem claim17_smul {α : Geo H M} (h : Claim17 α) (g : ↥(H ⊔ M)) : Claim17 (g • α) := by
  obtain ⟨x, hx, hxQ, hT⟩ := h
  refine ⟨(g : G) * x * (g : G)⁻¹, ?_, ?_, ?_⟩
  · rw [stab_smul]; exact mul_mem_conjSub hx
  · rw [Qv_smul, mem_conjSub]
    simpa [mul_assoc] using hxQ
  · unfold IsTransvec at hT ⊢
    rw [Zv_smul, Wn_smul, ← conjSub_zpowers, secIdx_conjSub]
    exact hT

theorem claim17_of_vtype_eq {α γ : Geo H M} (hv : vtype γ = vtype α) (h : Claim17 γ) :
    Claim17 α := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq hv
  exact claim17_smul h g

theorem conjSub_eq_of_mem_centralizer {g : G} {U : Subgroup G}
    (hg : g ∈ Subgroup.centralizer (U : Set G)) : conjSub g U = U := by
  have hc : ∀ u ∈ U, g * u * g⁻¹ = u := fun u hu => by
    rw [← Subgroup.mem_centralizer_iff.mp hg u hu]; group
  ext y
  rw [mem_conjSub]
  constructor
  · intro hy
    have h1 := hc _ hy
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [e] at h1
    rw [h1]; exact hy
  · intro hy
    have h1 := hc y hy
    have e : g⁻¹ * y * g = y := by
      calc g⁻¹ * y * g = g⁻¹ * (g * y * g⁻¹) * g := by rw [h1]
        _ = y := by group
    rw [e]; exact hy

theorem mem_normalizer_sup {g : G} {A B : Subgroup G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ {K : Subgroup G}, g ∈ Subgroup.normalizer (K : Set G) → conjSub g K = K := by
    intro K hK
    ext y
    rw [mem_conjSub]
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hK) y
    simp only [inv_inv] at h1
    exact h1.symm
  exact mem_normalizer_of_conjSub_eq (by rw [conjSub_sup, key hA, key hB])

theorem relIndex_zpowers_sup_le_two [Finite G] {A : Subgroup G} {c : G} (hc : c * c = 1)
    (hcA : c ∈ Subgroup.normalizer (A : Set G)) :
    A.relIndex (Subgroup.zpowers c ⊔ A) ≤ 2 := by
  rw [Sit43.relIndex_sup_of_le_normalizer (Subgroup.zpowers_le.mpr hcA)]
  have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc)
  refine Nat.le_of_dvd two_pos ((Subgroup.relIndex_dvd_card _ _).trans ?_)
  rwa [Nat.card_zpowers]

variable [Finite G]

theorem relIndex_ne_zero' (A B : Subgroup G) : A.relIndex B ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

theorem mem_Qv_of_comm_Wn (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {x : G} (hx : x ∈ stab α)
    (hxW : ∀ w ∈ Wn α, ⁅w, x⁆ ∈ Zv α) : x ∈ Qv α := by
  obtain ⟨δ, hδ⟩ := hs.exists_adj hA
  have hδ' : δ ∈ nbrs α := hδ
  obtain ⟨C, hC, hCX, hCn⟩ := exists_centralizer_quotient (X := stab α) (N := Wn α) (Z := Zv α)
    (stab_le_normalizer_Zv hA α) (stab_le_normalizer_Wn α)
  by_contra hxQ
  have hxC : x ∈ C := (hC x).mpr ⟨hx, hxW⟩
  have hCQ : ¬ C ≤ pCoreOf 2 (stab α) := fun h => hxQ (h hxC)
  have hT := sylow_stab_inf_left hA hδ'
  have hup := sup_sylow_eq_of_normal_not_le (Or.inr rfl) (quot_stab_five hA hs.vα) hT hCX hCn hCQ
  have hTn : stab α ⊓ stab δ ≤ Subgroup.normalizer (C : Set G) := inf_le_left.trans hCn
  have hL : Lres α ≤ C := oTwoRes_le_of_cover (X := stab α) (C := C) (Q := stab α ⊓ stab δ) hCn
    hT.2.1 hT.1 (fun y hy => by
      obtain ⟨c, hc, t, ht, e⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTn).mp (hup hy)
      exact ⟨c, hc, t, ht, e⟩)
  have hVW : Vn δ ≤ Wn α := hs.Vn_le_Wn hA h26 hδ'
  have hLV : ∀ l ∈ Lres α, ∀ v ∈ Vn δ, l * v * l⁻¹ ∈ Vn δ := by
    intro l hl v hv
    have h1 : ⁅v, l⁆ ∈ Zv α := ((hC l).mp (hL hl)).2 v (hVW hv)
    have e : l * v * l⁻¹ = ⁅v, l⁆⁻¹ * v := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Vn δ).mul_mem ((Vn δ).inv_mem (Sit43.Zv_le_Vn (α := α) hδ' h1)) hv
  have hTV : ∀ t ∈ stab α ⊓ stab δ, ∀ v ∈ Vn δ, t * v * t⁻¹ ∈ Vn δ := fun t ht v hv =>
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ ht.2) v).mp hv
  have hαV : stab α ≤ Subgroup.normalizer (Vn δ : Set G) := by
    refine Sit43.le_normalizer_of_conj_mem fun y hy v hv => ?_
    have hTL : stab α ⊓ stab δ ≤ Subgroup.normalizer (Lres α : Set G) :=
      inf_le_left.trans (le_normalizer_oTwoRes (stab α))
    obtain ⟨a, ha, t, ht, e⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTL).mp
      (le_oTwoRes_sup_of_isSylowTwoOf hT hy)
    have : y * v * y⁻¹ = a * (t * v * t⁻¹) * a⁻¹ := by rw [e]; group
    rw [this]
    exact hLV a ha _ (hTV t ht v hv)
  have hU : Vn δ ≤ stab α ⊓ stab δ := le_inf
    ((hs.Vn_le_Qv_of_nbr hA h26 hb hs.vα hδ').trans (pCoreOf_le 2 _))
    ((hs.Vn_le_Qv hδ').trans (pCoreOf_le 2 _))
  have hbot := eq_bot_of_normalizes_both hA hδ hU hαV (stab_le_normalizer_Vn δ)
  exact Zv_ne_bot hA α (le_bot_iff.mp (hbot ▸ Sit43.Zv_le_Vn (α := α) hδ'))

theorem isTransvec_of_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {K : Subgroup G} (hKW : K ≤ Wn α)
    (hK : K.relIndex (Wn α) ≤ 2) {x : G} (hx : x ∈ stab α) (hxQ : x ∉ Qv α)
    (hKx : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ Zv α) : IsTransvec 1 x (Zv α) (Wn α) := by
  have hWZ : Wn α ≤ Subgroup.normalizer (Zv α : Set G) :=
    ((hs.Wn_le_Qv hA hb).trans (pCoreOf_le 2 _)).trans (stab_le_normalizer_Zv hA α)
  have hxZ : x ∈ Subgroup.normalizer (Zv α : Set G) := stab_le_normalizer_Zv hA α hx
  have hmem : ∀ y, y ∈ fixSecIn (Subgroup.zpowers x) (Zv α) (Wn α) ↔
      y ∈ Wn α ∧ x * y * x⁻¹ * y⁻¹ ∈ Zv α := fun y => mem_fixSecIn_zpowers_iff hWZ hxZ
  have hKF : K ≤ fixSecIn (Subgroup.zpowers x) (Zv α) (Wn α) := fun k hk =>
    (hmem k).mpr ⟨hKW hk, hKx k hk⟩
  refine ⟨?_, ?_⟩
  · unfold secIdx
    by_contra hle
    have h0 := relIndex_ne_zero' (fixSecIn (Subgroup.zpowers x) (Zv α) (Wn α)) (Wn α)
    have h1 : (fixSecIn (Subgroup.zpowers x) (Zv α) (Wn α)).relIndex (Wn α) = 1 := by omega
    have hW := Subgroup.relIndex_eq_one.mp h1
    apply hxQ
    refine mem_Qv_of_comm_Wn hA h26 hs hb hx fun w hw => ?_
    have h2 := ((hmem w).mp (hW hw)).2
    have e : ⁅w, x⁆ = (x * w * x⁻¹ * w⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Zv α).inv_mem h2
  · unfold secIdx
    rw [pow_one]
    exact (Subgroup.relIndex_le_of_le_left hKF (relIndex_ne_zero' K (Wn α))).trans hK

theorem relIndex_inf_stab_le_two (hA : F53Amalgam H M S) {ρ δ ν : Geo H M}
    (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ) (hν : ν ∈ nbrs δ) {K : Subgroup G}
    (hK : K ≤ stab ρ ⊓ stab δ) : (K ⊓ stab ν).relIndex K ≤ 2 := by
  have h2 : (Qv δ).relIndex (stab ρ ⊓ stab δ) = 2 := Sit43.relIndex_Qv_edge hA hρ hδ
  have hQ : Qv δ ≤ stab ν := Qv_le_stab_of_mem_nbrs hA hν
  calc (K ⊓ stab ν).relIndex K ≤ (K ⊓ Qv δ).relIndex K :=
        Subgroup.relIndex_le_of_le_left (inf_le_inf_left _ hQ) (relIndex_ne_zero' _ _)
    _ = (Qv δ).relIndex K := by rw [inf_comm, Subgroup.inf_relIndex_right]
    _ ≤ (Qv δ).relIndex (stab ρ ⊓ stab δ) :=
        Subgroup.relIndex_le_of_le_right hK (by rw [h2]; norm_num)
    _ = 2 := h2

theorem comm_mem_Qst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) {ρ δ : Geo H M} (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ) {g d : G}
    (hg : g ∈ stab ρ ⊓ stab δ) (hd : d ∈ stab ρ ⊓ stab δ) : g * d * g⁻¹ * d⁻¹ ∈ Qst δ := by
  have hδv : vtype δ = true := Sit43.vtype_true_of_adj hρ hδ
  have h1 := (F53B1.commutator_sq_mem_of_relIndex_two (Sit43.relIndex_Qv_edge hA hρ hδ) hg hd).1
  have h2 := (F53B1.commutator_sq_mem_of_relIndex_two
    (hs.relIndex_edge_centralizer hA h26 hδv (nbrs_symm hδ)) hg hd).1
  exact ⟨h1, h2.2⟩

omit [Finite G] in
theorem conjSub_commutator (g : G) (A B : Subgroup G) :
    conjSub g ⁅A, B⁆ = ⁅conjSub g A, conjSub g B⁆ :=
  Subgroup.map_commutator _ _ _

theorem eq_of_Yv_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) {ε l l' : Geo H M} (hε : vtype ε = false) (hl : l ∈ nbrs ε)
    (hl' : l' ∈ nbrs ε) (hY : Yv l = Yv l') : l = l' := by
  have hlv : vtype l = true := Sit43.vtype_true_of_adj hε hl
  have hl'v : vtype l' = true := Sit43.vtype_true_of_adj hε hl'
  have hN := normalizer_Y (quot_stab_five hA hε) (sylow_stab_inf_left hA hl)
    (hs.of_vtype_false hε).orth
  rw [← hs.Yv_eq_comm_comm hA h26 hlv (nbrs_symm hl)] at hN
  obtain ⟨g, hgε, hgl⟩ := stab_transitive_on_nbrs hl hl'
  have hε' : conjSub (g : G) (stab ε) = stab ε := by
    rw [← stab_smul, smul_eq_of_mem_stab hgε]
  have hZ : conjSub (g : G) (Zv ε) = Zv ε := by
    rw [← Zv_smul, smul_eq_of_mem_stab hgε]
  have hP : conjSub (g : G) (stab ε ⊓ stab l) = stab ε ⊓ stab l' := by
    rw [conjSub_inf, hε', ← stab_smul, hgl]
  have hYc : conjSub (g : G) (Yv l) = Yv l' := by
    rw [hs.Yv_eq_comm_comm hA h26 hlv (nbrs_symm hl), hs.Yv_eq_comm_comm hA h26 hl'v
      (nbrs_symm hl'), conjSub_commutator, conjSub_commutator, hZ, hP]
  have hg : (g : G) ∈ stab ε ⊓ Subgroup.normalizer (Yv l : Set G) :=
    ⟨hgε, mem_normalizer_of_conjSub_eq (by rw [hYc, hY])⟩
  rw [hN] at hg
  rw [← hgl, smul_eq_of_mem_stab hg.2]

end C16

end CFSG.Quasithin.F53.Stellmacher.S43.Even
