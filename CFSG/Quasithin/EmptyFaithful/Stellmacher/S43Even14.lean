module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even14Fin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseB2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseD

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace C14

omit [Finite G] in
theorem commutator_le_of_le_normalizer {Z K : Subgroup G}
    (h : K ≤ Subgroup.normalizer (Z : Set G)) : ⁅Z, K⁆ ≤ Z := by
  rw [Subgroup.commutator_le]
  intro z hz k hk
  have h1 : k * z⁻¹ * k⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (h hk) z⁻¹).mp (Z.inv_mem hz)
  have e : ⁅z, k⁆ = z * (k * z⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [e]
  exact Z.mul_mem hz h1

omit [Finite G] in
theorem relIndex_le_two_of {K W : Subgroup G}
    (h : ∀ a ∈ W, a ∉ K → ∀ b ∈ W, b ∉ K → a⁻¹ * b ∈ K) : K.relIndex W ≤ 2 := by
  by_cases hW : W ≤ K
  · rw [Subgroup.relIndex_eq_one.mpr hW]
    omega
  · obtain ⟨a, haW, haK⟩ := IsConcreteLE.not_le_iff_exists.mp hW
    let f : Bool → ↥W ⧸ K.subgroupOf W := fun i =>
      if i then QuotientGroup.mk ⟨a, haW⟩ else QuotientGroup.mk 1
    have hf : Function.Surjective f := by
      intro c
      obtain ⟨⟨b, hbW⟩, rfl⟩ := QuotientGroup.mk_surjective c
      by_cases hbK : b ∈ K
      · refine ⟨false, ?_⟩
        show (QuotientGroup.mk 1 : ↥W ⧸ K.subgroupOf W) = QuotientGroup.mk ⟨b, hbW⟩
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using hbK
      · refine ⟨true, ?_⟩
        show (QuotientGroup.mk ⟨a, haW⟩ : ↥W ⧸ K.subgroupOf W) = QuotientGroup.mk ⟨b, hbW⟩
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        exact h a haW haK b hbW hbK
    have h2 := Nat.card_le_card_of_surjective f hf
    have hB : Nat.card Bool = 2 := by simp
    rw [hB] at h2
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact h2

variable {α : Geo H M}

theorem comm_Zv_crit_le (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    {α' : Geo H M} (hc : IsCritPair₁ α α') : ⁅Zv α, Zv α'⁆ ≤ Zv α :=
  commutator_le_of_le_normalizer ((hs.Zv_le_stab_crit' hA he hc).trans
    (stab_le_normalizer_Zv hA α))

theorem stab_inf_centralizer_Yv_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {μ l : Geo H M} (hμ : vtype μ = true) (hl : l ∈ nbrs μ) :
    stab l ⊓ Subgroup.centralizer (Yv μ : Set G) ≤ stab μ := by
  have hlv : vtype l = false := Sit43.vtype_false_of_adj hμ hl
  have hN := normalizer_Y (quot_stab_five hA hlv) (sylow_stab_inf_left hA (nbrs_symm hl))
    (hs.of_vtype_false hlv).orth
  rw [← hs.Yv_eq_comm_comm hA h26 hμ hl] at hN
  intro x hx
  have h1 : x ∈ stab l ⊓ Subgroup.normalizer (Yv μ : Set G) :=
    ⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩
  rw [hN] at h1
  exact h1.2

theorem Mab_le_centralizer_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {l μ : Geo H M} (hl : vtype l = false) (hμ : μ ∈ nbrs l) :
    Mab l μ ≤ Subgroup.centralizer (Zv μ : Set G) := by
  obtain ⟨D⟩ := (hs.of_vtype_false hl).exists_dict hA hμ
  have hμv : vtype μ = true := Sit43.vtype_true_of_adj hl hμ
  rw [← hs.Zv_inf_centralizer hA h26 hμv (nbrs_symm hμ)]
  intro x hx
  have hxl : x ∈ stab l := Mab_le_stab l μ hx
  exact mem_centralizer_fix D ⟨x, hxl⟩ ((Sit43.mem_Mab_iff D ⟨x, hxl⟩).mp hx)

theorem Wn_le_stab_of_dist (hA : F53Amalgam H M S) (hs : Sit43 α) {ρ : Geo H M}
    (hρ : dist α ρ + 2 ≤ bMin H M) : Wn α ≤ stab ρ :=
  iSup₂_le fun l hl => hs.Zv_le_stab_of_dist_le_false hA (hs.vtype_of_dist_two hA hl) (by
    have := dist_triangle hA.amalgam.gen l α ρ
    omega)

theorem pow_four_of_mem_Wn (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 4 ≤ bMin H M) {w : G} (hw : w ∈ Wn α) : w ^ 4 = 1 := by
  have h2 := (isElemAbelian_Zv hA α).2 _ (hs.sq_mem_Zv hA h26 hb w hw)
  rw [← pow_mul] at h2
  exact h2

theorem relIndex_Wn_of_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) (hb : 4 ≤ bMin H M) {α' ν ρ : Geo H M} (hc : IsCritPair₁ α α')
    (hν : ν ∈ nbrs α') (hd : dist α ν < bMin H M) (hρ : ρ ∈ nbrs ν) (hWρ : Wn α ≤ stab ρ)
    (h2 : (Zv α ⊓ Qv α').relIndex (Zv α) = 2) : (stab ν).relIndex (Wn α) ≤ 2 := by
  have hα'v : vtype α' = false := hs.vtype_crit hA he hc
  have hνv : vtype ν = true := Sit43.vtype_true_of_adj hα'v hν
  have hρv : vtype ρ = false := Sit43.vtype_false_of_adj hνv hρ
  obtain ⟨hcard, hne, hsup⟩ := hs.comm_of_two hA h26 he hc hν hd h2
  have hR₁Y : ⁅Zv α, Zv α'⁆ ≤ Yv ν := by
    rw [← hsup]
    exact le_sup_left
  have hnle : ¬ ⁅Zv α, Zv α'⁆ ≤ Zv ν := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge h (by rw [hcard, hs.card_Zv_true hA h26 hνv]))
  obtain ⟨y, hyR, hyZ⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  obtain ⟨D⟩ := (hs.of_vtype_false hρv).exists_dict hA (nbrs_symm hρ)
  have hyY : y ∈ ⁅⁅Zv ρ, stab ρ ⊓ stab ν⁆, stab ρ ⊓ stab ν⁆ := by
    rw [← hs.Yv_eq_comm_comm hA h26 hνv hρ]
    exact hR₁Y hyR
  have hyC : y ∉ Zv ρ ⊓ Subgroup.centralizer ((stab ρ ⊓ stab ν : Subgroup G) : Set G) := by
    rw [hs.Zv_inf_centralizer hA h26 hνv hρ]
    exact hyZ
  have hWR : Wn α ≤ Subgroup.centralizer ((⁅Zv α, Zv α'⁆ : Subgroup G) : Set G) :=
    (hs.Wn_le_centralizer hA (by omega)).trans
      (Subgroup.centralizer_le (comm_Zv_crit_le hA hs he hc))
  have hcomm : ∀ w ∈ Wn α, w * y = y * w := fun w hw =>
    (Subgroup.mem_centralizer_iff.mp (hWR hw) y hyR).symm
  have pow4 : ∀ {w : G}, w ∈ Wn α → w ^ 4 = 1 := fun hw => pow_four_of_mem_Wn hA h26 hs hb hw
  refine relIndex_le_two_of fun a ha haν b hb' hbν => ?_
  exact (inv_mul_mem_of_commute D hyY hyC (hWρ ha) (hWρ hb') (hcomm a ha) (hcomm b hb')
    (pow4 ha) (pow4 hb') (pow4 (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hb'))
    (fun h => haν h.2) (fun h => hbν h.2)).2

end C14

open C14 in
theorem claim14 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (he : Even (bMin H M)) (hb : 4 ≤ bMin H M) : Claim14 α := by
  intro α' ν ρ hc hν hdν hρ hdρ
  have hα'v : vtype α' = false := hs.vtype_crit hA he hc
  have hνv : vtype ν = true := Sit43.vtype_true_of_adj hα'v hν
  have hρv : vtype ρ = false := Sit43.vtype_false_of_adj hνv hρ
  have hd : dist α ν < bMin H M := by omega
  have hWρ : Wn α ≤ stab ρ := Wn_le_stab_of_dist hA hs (by omega)
  have hWR : Wn α ≤ Subgroup.centralizer ((⁅Zv α, Zv α'⁆ : Subgroup G) : Set G) :=
    (hs.Wn_le_centralizer hA (by omega)).trans
      (Subgroup.centralizer_le (comm_Zv_crit_le hA hs he hc))
  have h3 : stab ρ ⊓ Subgroup.centralizer (Yv ν : Set G) ≤ stab ν :=
    stab_inf_centralizer_Yv_le hA h26 hs hνv hρ
  have h4 : Wn α ⊓ Mab ρ ν ≤ Subgroup.centralizer (Yv ν : Set G) := by
    rcases hs.relIndex_Zv_two_or_four hA h26 he hc hν hd with h2 | h4
    · obtain ⟨-, -, hsup⟩ := hs.comm_of_two hA h26 he hc hν hd h2
      have hM : Wn α ⊓ Mab ρ ν ≤ Subgroup.centralizer (Zv ν : Set G) :=
        inf_le_right.trans (Mab_le_centralizer_Zv hA h26 hs hρv (nbrs_symm hρ))
      rw [← hsup, Subgroup.le_centralizer_iff]
      exact sup_le (Subgroup.le_centralizer_iff.mp (inf_le_left.trans hWR))
        (Subgroup.le_centralizer_iff.mp hM)
    · rw [← hs.comm_eq_Yv_of_four hA h26 he hc hν hd h4]
      exact inf_le_left.trans hWR
  have h5 : Wn α ⊓ Mab ρ ν ≤ stab ν := fun x hx => h3 ⟨Mab_le_stab ρ ν hx.2, h4 hx⟩
  refine ⟨hWρ, ?_, h3, h4, h5⟩
  rw [Subgroup.inf_relIndex_left]
  rcases hs.relIndex_Zv_two_or_four hA h26 he hc hν hd with h2 | h4
  · exact relIndex_Wn_of_two hA h26 hs he hb hc hν hd hρ hWρ h2
  · have hY := hs.comm_eq_Yv_of_four hA h26 he hc hν hd h4
    have hle : Wn α ≤ stab ν := fun w hw => h3 ⟨hWρ hw, by rw [← hY]; exact hWR hw⟩
    rw [Subgroup.relIndex_eq_one.mpr hle]
    omega

namespace C14

variable {α : Geo H M}

theorem comm_mem_Zv_of_conj_eq (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    {α' : Geo H M} (hc : IsCritPair₁ α α') {x h : G} (hx : x ∈ Zv α')
    (hh : ∃ a ∈ Zv α, h * x * h⁻¹ = a * x * a⁻¹) : h * x * h⁻¹ * x⁻¹ ∈ Zv α := by
  obtain ⟨a, ha, e⟩ := hh
  rw [e]
  exact comm_Zv_crit_le hA hs he hc (Subgroup.commutator_mem_commutator ha hx)

theorem comm_mem_Zv_of_le (hA : F53Amalgam H M S) (hs : Sit43 α) (he : Even (bMin H M))
    {α' : Geo H M} (hc : IsCritPair₁ α α') (hH : Wn α ⊓ stab α' ≤ Zv α ⊔ Qv α') {x : G}
    (hx : x ∈ Zv α') : ∀ h ∈ Wn α ⊓ stab α', h * x * h⁻¹ * x⁻¹ ∈ Zv α := by
  intro h hh
  refine comm_mem_Zv_of_conj_eq hA hs he hc hx ?_
  have hZα' : Zv α ≤ stab α' := hs.Zv_le_stab_crit hA hc
  have hn : Zv α ≤ Subgroup.normalizer (Qv α' : Set G) :=
    hZα'.trans (le_normalizer_pCoreOf 2 _)
  have hh' : h ∈ Qv α' ⊔ Zv α := by
    rw [sup_comm]
    exact hH hh
  obtain ⟨q, hq, a, ha, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hn).mp hh'
  refine ⟨a, ha, ?_⟩
  have hax : a * x * a⁻¹ ∈ Zv α' :=
    (Subgroup.mem_normalizer_iff.mp ((hZα'.trans (stab_le_normalizer_Zv hA α')) ha) x).mp hx
  have hqc : a * x * a⁻¹ * q = q * (a * x * a⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA α' hq) _ hax
  calc q * a * x * (q * a)⁻¹ = q * (a * x * a⁻¹) * q⁻¹ := by group
    _ = a * x * a⁻¹ * q * q⁻¹ := by rw [← hqc]
    _ = a * x * a⁻¹ := by group

theorem le_sup_of_four (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) (hb : 4 ≤ bMin H M) {α' ν : Geo H M} (hc : IsCritPair₁ α α')
    (hν : ν ∈ nbrs α') (hd : dist α ν < bMin H M)
    (h4 : (Zv α ⊓ Qv α').relIndex (Zv α) = 4) : Wn α ⊓ stab α' ≤ Zv α ⊔ Qv α' := by
  have hνv : vtype ν = true := Sit43.vtype_true_of_adj (hs.vtype_crit hA he hc) hν
  have hWR : Wn α ≤ Subgroup.centralizer ((⁅Zv α, Zv α'⁆ : Subgroup G) : Set G) :=
    (hs.Wn_le_centralizer hA (by omega)).trans
      (Subgroup.centralizer_le (comm_Zv_crit_le hA hs he hc))
  intro h hh
  rw [hs.Zv_sup_Qv_eq_of_four hA h26 he hc hν hd h4]
  have hhY : h ∈ Subgroup.centralizer (Yv ν : Set G) := by
    rw [← hs.comm_eq_Yv_of_four hA h26 he hc hν hd h4]
    exact hWR hh.1
  exact ⟨⟨hh.2, stab_inf_centralizer_Yv_le hA h26 hs hνv (nbrs_symm hν) ⟨hh.2, hhY⟩⟩, hhY⟩

theorem exists_of_not_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (he : Even (bMin H M)) (hb : 4 ≤ bMin H M) {α' : Geo H M} (hc : IsCritPair₁ α α')
    (hH : ¬ Wn α ⊓ stab α' ≤ Zv α ⊔ Qv α') :
    ∃ x ∈ Zv α', x ∉ Qv α ∧ ∀ h ∈ Wn α ⊓ stab α', h * x * h⁻¹ * x⁻¹ ∈ Zv α := by
  obtain ⟨ν, hν, hdν⟩ := hs.exists_nbr_dist hA hc
  have hd : dist α ν < bMin H M := by omega
  have h2 : (Zv α ⊓ Qv α').relIndex (Zv α) = 2 :=
    (hs.relIndex_Zv_two_or_four hA h26 he hc hν hd).resolve_right fun h4 =>
      hH (le_sup_of_four hA h26 hs he hb hc hν hd h4)
  obtain ⟨y, hyH, hyZQ⟩ := IsConcreteLE.not_le_iff_exists.mp hH
  obtain ⟨z, hz, hzQ, hzidx, -⟩ := hs.exists_transposition_of_two hA h26 he hc hν hd h2
  obtain ⟨D⟩ := (hs.sit_crit hA he hc).exists_dict hA hν
  have hzS : z ∈ stab α' ⊓ stab ν :=
    (hs.Zv_le_Qv_crit_nbr hA hν hd).2 ((hs.Zv_le_Qv_crit_nbr hA hν hd).1 hz)
  have hWR : Wn α ≤ Subgroup.centralizer ((⁅Zv α, Zv α'⁆ : Subgroup G) : Set G) :=
    (hs.Wn_le_centralizer hA (by omega)).trans
      (Subgroup.centralizer_le (comm_Zv_crit_le hA hs he hc))
  have hcz : ∀ g ∈ Wn α, ∀ w ∈ Zv α', g * ⁅z, w⁆ = ⁅z, w⁆ * g := fun g hg w hw =>
    (Subgroup.mem_centralizer_iff.mp (hWR hg) _ (Subgroup.commutator_mem_commutator hz hw)).symm
  have hy1 : y ∉ pCoreOf 2 (stab α') := fun h => hyZQ (Subgroup.mem_sup_right h)
  have hyz : z⁻¹ * y ∉ pCoreOf 2 (stab α') := fun h => hyZQ (by
    have e : y = z * (z⁻¹ * y) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hz h)
  have pow4 : ∀ {w : G}, w ∈ Wn α → w ^ 4 = 1 := fun hw => pow_four_of_mem_Wn hA h26 hs hb hw
  obtain ⟨x, hx, hxz, hxP⟩ := exists_of_transposition D hzS hzQ hzidx hyH.2 (pow4 hyH.1)
    (hcz y hyH.1) hy1 hyz
  refine ⟨x, hx, fun hxQ => hxz ?_, fun h hh => comm_mem_Zv_of_conj_eq hA hs he hc hx ?_⟩
  · exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hz).2 x hxQ).symm
  · rcases hxP h hh.2 (pow4 hh.1) (pow4 (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyH.1) hh.1))
      (hcz h hh.1) with h1 | h1
    · exact ⟨1, one_mem _, by rw [h1]; group⟩
    · refine ⟨z⁻¹, inv_mem hz, ?_⟩
      calc h * x * h⁻¹ = z⁻¹ * (z * h * x) * h⁻¹ := by group
        _ = z⁻¹ * (x * (z * h)) * h⁻¹ := by rw [h1]
        _ = z⁻¹ * x * z⁻¹⁻¹ := by group

end C14

open C14 in
theorem claim15 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (he : Even (bMin H M)) (hb : 4 ≤ bMin H M) : Claim15 α := by
  intro α' hc
  by_cases hH : Wn α ⊓ stab α' ≤ Zv α ⊔ Qv α'
  · obtain ⟨x, hx, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp (hs.not_Zv_le_Qv_crit hA he hc)
    exact ⟨x, hx, hxQ, comm_mem_Zv_of_le hA hs he hc hH hx⟩
  · exact exists_of_not_le hA h26 hs he hb hc hH

end CFSG.Quasithin.F53.Stellmacher.S43.Even
