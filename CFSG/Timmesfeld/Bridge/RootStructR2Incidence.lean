module

public import CFSG.Timmesfeld.Bridge.RootStructR2Defs2
public import CFSG.Timmesfeld.Bridge.RootStructWTICard

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

@[expose] def linePoints (D : Set G) (L : Subgroup G) : Set (Subgroup G) :=
  {P | ∃ u ∈ D, u ∈ L ∧ P = rootGroup D u}

theorem card_rootGroup_eq (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {a b : G} (ha : a ∈ D)
    (hb : b ∈ D) : Nat.card (rootGroup D a) = Nat.card (rootGroup D b) := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_isClass hclass ha hb)
  rw [rootGroup_conj hclass]
  exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm

theorem exists_map_conj_eq_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) {S : Set (Subgroup G)}
    (hS : ∀ g ∈ P, ∀ H ∈ S, H.map (MulAut.conj g).toMonoidHom ∈ S) (hpS : ¬ p ∣ S.ncard) :
    ∃ H ∈ S, ∀ g ∈ P, H.map (MulAut.conj g).toMonoidHom = H := by
  let act : MulAction P S :=
    { smul := fun g H => ⟨(H : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom,
        hS g g.2 H H.2⟩
      one_smul := fun H => Subtype.ext (by
        change (H : Subgroup G).map (MulAut.conj (1 : G)).toMonoidHom = H
        rw [map_one]
        exact Subgroup.map_id _)
      mul_smul := fun g g' H => Subtype.ext (by
        change (H : Subgroup G).map (MulAut.conj ((g : G) * g')).toMonoidHom =
          ((H : Subgroup G).map (MulAut.conj (g' : G)).toMonoidHom).map
            (MulAut.conj (g : G)).toMonoidHom
        rw [Subgroup.map_map, map_mul]
        rfl) }
  have hcard : ¬ p ∣ Nat.card S := by rwa [Nat.card_coe_set_eq]
  obtain ⟨⟨H, hH⟩, hfix⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card S hcard
  refine ⟨H, hH, fun g hg => ?_⟩
  have := congrArg Subtype.val (hfix ⟨g, hg⟩)
  exact this

section Lines

variable (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
include h hc hs

theorem ncard_linePoints {a d : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) :
    (linePoints D (rootGroup D a ⊔ rootGroup D d)).ncard = Nat.card (rootGroup D a) + 1 := by
  classical
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  set L := rootGroup D a ⊔ rootGroup D d with hL
  set q := Nat.card (rootGroup D a) with hq
  set S := linePoints D L with hS
  have hcardP : ∀ P ∈ S, Nat.card P = q := by
    rintro P ⟨u, hu, -, rfl⟩
    exact card_rootGroup_eq hclass hu ha
  have hunion : (L : Set G) \ {1} = ⋃ P ∈ S, (P : Set G) \ {1} := by
    ext v
    simp only [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff, Set.mem_iUnion,
      exists_prop]
    constructor
    · rintro ⟨hvL, hv1⟩
      have hvD := mem_of_mem_sup_rootGroup h hc hs ha hd had hadD hdT hvL hv1
      exact ⟨rootGroup D v, ⟨v, hvD, hvL, rfl⟩,
        rootSet_subset_rootGroup D v (mem_rootSet_self hvD), hv1⟩
    · rintro ⟨P, ⟨u, hu, huL, rfl⟩, hvP, hv1⟩
      exact ⟨rootGroup_le_sup_of_mem h hc hs ha hd had hadD hdT huL (hD.ne_one hu) hvP, hv1⟩
  have hdisj : S.PairwiseDisjoint (fun P => (P : Set G) \ {1}) := by
    rintro P ⟨u, hu, -, rfl⟩ P' ⟨u', hu', -, rfl⟩ hne
    refine Set.disjoint_left.2 fun v hv hv' => hne ?_
    have hvT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hu hv.1 hv.2
    have hvT' := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hu' hv'.1 hv'.2
    rw [← rootGroup_eq_of_mem hvT, ← rootGroup_eq_of_mem hvT']
  have hpiece : ∀ P ∈ S, ((P : Set G) \ {1}).ncard = q - 1 := by
    intro P hP
    rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem P), ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) (hcardP P hP)
  have hcount : ((L : Set G) \ {1}).ncard = S.ncard * (q - 1) := by
    rw [hunion, (Set.toFinite S).ncard_biUnion (fun _ _ => Set.toFinite _) hdisj,
      finsum_mem_congr rfl hpiece, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite S),
      Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card S (Set.toFinite S)]
  have hLcard : ((L : Set G) \ {1}).ncard = q * q - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem L), ← Nat.card_coe_set_eq]
    change Nat.card L - 1 = q * q - 1
    rw [hL, card_sup_rootGroup h hc ha hd had hdT, card_rootGroup_eq hclass hd ha]
  have hq2 : 2 ≤ q := by
    have h2 : a ∈ rootGroup D a := rootSet_subset_rootGroup D a (mem_rootSet_self ha)
    have hne : rootGroup D a ≠ ⊥ := fun e => hD.ne_one ha (by rw [e] at h2; exact h2)
    exact (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  rw [hcount] at hLcard
  obtain ⟨r, hr⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  rw [hr] at hLcard ⊢
  have e1 : (r + 2) * (r + 2) - 1 = (r + 3) * (r + 1) := by
    rw [show (r + 2) * (r + 2) = (r + 3) * (r + 1) + 1 by ring]
    omega
  rw [e1, show r + 2 - 1 = r + 1 by omega] at hLcard
  exact Nat.eq_of_mul_eq_mul_right (by omega) hLcard

theorem ncard_linePoints_diff {a d : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) :
    (linePoints D (rootGroup D a ⊔ rootGroup D d) \ {rootGroup D a}).ncard =
      Nat.card (rootGroup D a) := by
  have hmem : rootGroup D a ∈ linePoints D (rootGroup D a ⊔ rootGroup D d) :=
    ⟨a, ha, left_mem_line ha, rfl⟩
  rw [Set.ncard_sdiff_singleton_of_mem hmem, ncard_linePoints h hc hs ha hd had hadD hdT,
    Nat.add_sub_cancel]

omit hs in
theorem collinear_of_mem_rootSet (hs : SpecialClosure D) {c c' b : G} (hcD : c ∈ D)
    (hc' : c' ∈ rootSet D c) (hb : b ∈ D) (hcb : Commute c b) (hcbD : c * b ∈ D)
    (hbT : b ∉ rootSet D c) : Commute c' b ∧ c' * b ∈ D := by
  have hD := h.root
  have hc'b : Commute c' b := (hc'.2 b hb).2 hcb
  refine ⟨hc'b, mem_of_mem_sup_rootGroup h hc hs hcD hb hcb hcbD hbT
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left (rootSet_subset_rootGroup D c hc'))
      (right_mem_line hb)) fun h1 => hbT ?_⟩
  rw [show b = c'⁻¹ from eq_inv_of_mul_eq_one_right h1, hD.inv_eq hc'.1]
  exact hc'

theorem rootLines_eq_of_mem_rootSet {c c' : G} (hcD : c ∈ D) (hc' : c' ∈ rootSet D c) :
    rootLines D c' = rootLines D c := by
  have hcc' : c ∈ rootSet D c' := mem_rootSet_comm hcD hc'
  have key : ∀ {x y : G}, x ∈ D → y ∈ rootSet D x → ∀ L ∈ rootLines D x, L ∈ rootLines D y := by
    rintro x y hx hy L ⟨b, hb, hxb, hxbD, hbT, rfl⟩
    obtain ⟨hyb, hybD⟩ := collinear_of_mem_rootSet h hc hs hx hy hb hxb hxbD hbT
    refine ⟨b, hb, hyb, hybD, by rwa [rootSet_eq_of_mem hy], ?_⟩
    rw [rootGroup_eq_of_mem hy]
  ext L
  exact ⟨key hc'.1 hcc' L, key hcD hc' L⟩

theorem mem_rootLines_of_mem {a d x : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hx : x ∈ D)
    (hxL : x ∈ rootGroup D a ⊔ rootGroup D d) :
    rootGroup D a ⊔ rootGroup D d ∈ rootLines D x := by
  have hD := h.root
  by_cases hxa : x ∈ rootSet D a
  · rw [rootLines_eq_of_mem_rootSet h hc hs ha hxa]
    exact ⟨d, hd, had, hadD, hdT, rfl⟩
  · have hax := commute_of_mem_sup_rootGroup ha hd had (left_mem_line ha) hxL
    have hxa1 : x * a ≠ 1 := fun h' => hxa (by
      rw [show x = a⁻¹ from eq_inv_of_mul_eq_one_left h', hD.inv_eq ha]
      exact mem_rootSet_self ha)
    refine ⟨a, ha, hax.symm, mem_of_mem_sup_rootGroup h hc hs ha hd had hadD hdT
      (Subgroup.mul_mem _ hxL (left_mem_line ha)) hxa1, fun h' => hxa (mem_rootSet_comm hx h'), ?_⟩
    rw [sup_comm (rootGroup D x)]
    exact (sup_rootGroup_eq_of_mem h hc hs ha hd had hadD hdT (left_mem_line ha) hxL
      (hD.ne_one ha) (hD.ne_one hx) hxa).symm

theorem mem_rootLines_of_mem_rootLines {c x : G} (hcD : c ∈ D) {L : Subgroup G}
    (hL : L ∈ rootLines D c) (hx : x ∈ D) (hxL : x ∈ L) : L ∈ rootLines D x := by
  obtain ⟨b, hb, hcb, hcbD, hbT, rfl⟩ := hL
  exact mem_rootLines_of_mem h hc hs hcD hb hcb hcbD hbT hx hxL

theorem eq_of_mem_linePoints_of_mem_linePoints {c : G} (hcD : c ∈ D) {L L' : Subgroup G}
    (hL : L ∈ rootLines D c) (hL' : L' ∈ rootLines D c) (hne : L ≠ L') {P : Subgroup G}
    (hP : P ∈ linePoints D L) (hP' : P ∈ linePoints D L') : P = rootGroup D c := by
  have hD := h.root
  obtain ⟨b, hb, hcb, hcbD, hbT, rfl⟩ := hL
  obtain ⟨b', hb', hcb', hcb'D, hb'T, rfl⟩ := hL'
  obtain ⟨u, hu, huL, rfl⟩ := hP
  obtain ⟨u', hu', huL', hu'u⟩ := hP'
  by_contra huc
  have huT : u ∉ rootSet D c := fun h' => huc (rootGroup_eq_of_mem h')
  apply hne
  have h1 := sup_rootGroup_eq_of_mem h hc hs hcD hb hcb hcbD hbT (left_mem_line hcD) huL
    (hD.ne_one hcD) (hD.ne_one hu) huT
  have huL'' : u ∈ rootGroup D c ⊔ rootGroup D b' :=
    rootGroup_le_sup_of_mem h hc hs hcD hb' hcb' hcb'D hb'T huL' (hD.ne_one hu')
      (hu'u ▸ rootSet_subset_rootGroup D u (mem_rootSet_self hu))
  have h2 := sup_rootGroup_eq_of_mem h hc hs hcD hb' hcb' hcb'D hb'T (left_mem_line hcD) huL''
    (hD.ne_one hcD) (hD.ne_one hu) huT
  rw [← h1, ← h2]

theorem map_conj_mem_rootLines_of_map_eq {c : G} (hcD : c ∈ D) {g : G}
    (hg : (rootGroup D c).map (MulAut.conj g).toMonoidHom = rootGroup D c) {L : Subgroup G}
    (hL : L ∈ rootLines D c) : L.map (MulAut.conj g).toMonoidHom ∈ rootLines D c := by
  have := h.finite
  have h1 := map_conj_mem_rootLines_conj h.isClass hL g
  have hgc : g * c * g⁻¹ ∈ rootSet D c := by
    have hmem : g * c * g⁻¹ ∈ rootGroup D c := by
      rw [← hg]
      exact ⟨c, rootSet_subset_rootGroup D c (mem_rootSet_self hcD), rfl⟩
    exact mem_rootSet_of_mem_rootGroup_of_ne_one h.root hc hcD hmem
      (h.root.ne_one (conj_mem_of_isClass h.isClass g hcD))
  rwa [rootLines_eq_of_mem_rootSet h hc hs hcD hgc] at h1

end Lines

theorem map_conj_mem_linePoints (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {L P : Subgroup G}
    (hP : P ∈ linePoints D L) (g : G) :
    P.map (MulAut.conj g).toMonoidHom ∈ linePoints D (L.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨u, hu, huL, rfl⟩ := hP
  exact ⟨g * u * g⁻¹, conj_mem_of_isClass hclass g hu, ⟨u, huL, rfl⟩,
    (rootGroup_conj hclass g u).symm⟩

theorem isPGroup_rootGroup [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) {a : G} (ha : a ∈ D) :
    IsPGroup 2 (rootGroup D a) := by
  refine (Moufang.isPGroup_twoCore a).to_le ?_
  rw [rootGroup, Subgroup.closure_le]
  exact fun x hx => (rootSet_subset_twoCore_self hclass hD hc ha x hx).2

theorem not_dvd_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ) : ¬ p ∣ 2 ^ m := fun h' =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h'))

theorem mem_gatedPoints_of_path (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) {a c e x : G} (ha : a ∈ D)
    (hcD : c ∈ D) (heD : e ∈ D) (hxD : x ∈ D) {T L₂ L₃ : Subgroup G} (hT : T ∈ rootLines D a)
    (hcT : c ∈ T) (hca : rootGroup D c ∉ ({rootGroup D a} : Set (Subgroup G)))
    (hL₂ : L₂ ∈ rootLines D c) (hL₂T : L₂ ∉ ({T} : Set (Subgroup G))) (heL₂ : e ∈ L₂)
    (hec : rootGroup D e ∉ ({rootGroup D c} : Set (Subgroup G))) (hL₃ : L₃ ∈ rootLines D e)
    (hL₃L₂ : L₃ ∉ ({L₂} : Set (Subgroup G))) (hxL₃ : x ∈ L₃)
    (hxe : rootGroup D x ∉ ({rootGroup D e} : Set (Subgroup G))) :
    rootGroup D x ∈ gatedPoints D a T := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  rw [Set.mem_singleton_iff] at hca hL₂T hec hL₃L₂ hxe
  have hcol : ∀ {u v : G} {L : Subgroup G}, u ∈ D → v ∈ D → L ∈ rootLines D u → v ∈ L →
      rootGroup D v ≠ rootGroup D u →
      Commute u v ∧ u * v ∈ D ∧ v ∉ rootSet D u ∧ rootGroup D u ⊔ rootGroup D v = L := by
    intro u v L hu hv hL hvL hvu
    obtain ⟨b, hb, hub, hubD, hbT, rfl⟩ := hL
    have hvT : v ∉ rootSet D u := fun h' => hvu (rootGroup_eq_of_mem h')
    refine ⟨commute_of_mem_sup_rootGroup hu hb hub (left_mem_line hu) hvL,
      mem_of_mem_sup_rootGroup h hc hs hu hb hub hubD hbT (Subgroup.mul_mem _ (left_mem_line hu)
        hvL) fun h1 => hvT ?_, hvT, sup_rootGroup_eq_of_mem h hc hs hu hb hub hubD hbT
        (left_mem_line hu) hvL (hD.ne_one hu) (hD.ne_one hv) hvT⟩
    rw [show v = u⁻¹ from eq_inv_of_mul_eq_one_right h1, hD.inv_eq hu]
    exact mem_rootSet_self hu
  obtain ⟨hac, hacD, hcTa, hTeq⟩ := hcol ha hcD hT hcT hca
  obtain ⟨hce, hceD, heTc, hL₂eq⟩ := hcol hcD heD hL₂ heL₂ hec
  obtain ⟨hex, hexD, hxTe, hL₃eq⟩ := hcol heD hxD hL₃ hxL₃ hxe
  have hTc := mem_rootLines_of_mem_rootLines h hc hs ha hT hcD hcT
  have hL₂e := mem_rootLines_of_mem_rootLines h hc hs hcD hL₂ heD heL₂
  have heT : e ∉ T := fun heT => hec (eq_of_mem_linePoints_of_mem_linePoints h hc hs hcD hL₂ hTc
    hL₂T ⟨e, heD, heL₂, rfl⟩ ⟨e, heD, heT, rfl⟩)
  have hxL₂ : x ∉ L₂ := fun hxL₂ => hxe (eq_of_mem_linePoints_of_mem_linePoints h hc hs heD hL₃
    hL₂e hL₃L₂ ⟨x, hxD, hxL₃, rfl⟩ ⟨x, hxD, hxL₂, rfl⟩)
  have hLac := hAll a ha c hcD hac hacD hcTa
  have hLce := hAll c hcD e heD hce hceD heTc
  have hae : ¬ Commute a e := fun hae => heT (by
    rw [← hTeq]
    exact mem_sup_of_commute_of_lineTI h hc hs hconn ha hcD hac hacD hcTa hLac heD hae.symm
      hce.symm)
  have hcx : ¬ Commute c x := fun hcx => hxL₂ (by
    rw [← hL₂eq]
    exact mem_sup_of_commute_of_lineTI h hc hs hconn hcD heD hce hceD heTc hLce hxD hcx.symm
      hex.symm)
  have hecD : e * c ∈ D := by rw [← hce.eq]; exact hceD
  have hxeD : x * e ∈ D := by rw [← hex.eq]; exact hexD
  have h4ae : orderOf (a * e) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD ha heD with h' | h' | ⟨hodd, -⟩
    · exact absurd h' hae
    · exact h'
    · exact absurd hac (not_commute_of_collinear hD ha hcD hae hodd hce.symm hecD)
  have h4cx : orderOf (x * c) = 4 := by
    rw [orderOf_mul_comm_eq]
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hcD hxD with h' | h' | ⟨hodd, -⟩
    · exact absurd h' hcx
    · exact h'
    · exact absurd hce (not_commute_of_collinear hD hcD heD hcx hodd hex.symm hxeD)
  have hcz : c ∈ rootSet D ((a * e) ^ 2) :=
    mem_rootSet_sq_of_lineTI h hc hs ha heD hcD h4ae hac hacD hce.symm hLac
  obtain ⟨hzD, haz, hez, -⟩ := sq_mem_of_orderOf_eq_four hD ha heD h4ae
  have h4ea : orderOf (e * a) = 4 := by rwa [orderOf_mul_comm_eq]
  have hzeD : (a * e) ^ 2 * e ∈ D := by
    rw [← hez.eq, mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one ha) (hD.mul_self_eq_one heD) h4ae]
    exact mul_sq_mem_of_orderOf_eq_four hclass hD heD ha h4ea
  have heTz : e ∉ rootSet D ((a * e) ^ 2) := fun h' => hae ((h'.2 a ha).2 haz.symm).symm
  have hxz : ¬ Commute x ((a * e) ^ 2) := fun h' => hcx ((hcz.2 x hxD).2 h'.symm)
  have hopp := opposite_of_lineTI h hc hs ha heD hxD h4ae hex hxz
    (hAll _ hzD e heD hez.symm hzeD heTz)
  exact ⟨⟨x, hxD, rfl, hopp.1, hopp.2, c, hcD, hac, hacD, h4cx⟩, x, hxD, rfl, c, hcD, hcT, h4cx⟩

section Fixed

variable (hL : LineSetting G D)
include hL

theorem LineSetting.not_dvd_card_rootGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : G}
    (hcD : c ∈ D) : ¬ p ∣ Nat.card (rootGroup D c) := by
  have := hL.hyp.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (isPGroup_rootGroup hL.hyp.isClass hL.hyp.root
    hL.closure hcD)
  rw [hn]
  exact not_dvd_two_pow hp hp2 n

theorem LineSetting.exists_fixed_linePoints {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup p P) {c : G} (hcD : c ∈ D) {L : Subgroup G}
    (hLc : L ∈ rootLines D c)
    (hPc : ∀ g ∈ P, (rootGroup D c).map (MulAut.conj g).toMonoidHom = rootGroup D c)
    (hPL : ∀ g ∈ P, L.map (MulAut.conj g).toMonoidHom = L) :
    ∃ E ∈ linePoints D L \ {rootGroup D c}, ∀ g ∈ P, E.map (MulAut.conj g).toMonoidHom = E := by
  have := hL.hyp.finite
  have hclass := hL.hyp.isClass
  obtain ⟨b, hb, hcb, hcbD, hbT, rfl⟩ := hLc
  refine exists_map_conj_eq_of_isPGroup hP (fun g hg E hE => ⟨?_, fun h' => hE.2 ?_⟩) ?_
  · have := map_conj_mem_linePoints hclass hE.1 g
    rwa [hPL g hg] at this
  · rw [Set.mem_singleton_iff] at h' ⊢
    exact Subgroup.map_injective (MulAut.conj g).injective (h'.trans (hPc g hg).symm)
  · rw [ncard_linePoints_diff hL.hyp hL.closure hL.special hcD hb hcb hcbD hbT]
    exact hL.not_dvd_card_rootGroup hp.out hp2 hcD

theorem LineSetting.exists_fixed_rootLines {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup p P) {c : G} (hcD : c ∈ D) {L : Subgroup G}
    (hLc : L ∈ rootLines D c)
    (hPc : ∀ g ∈ P, (rootGroup D c).map (MulAut.conj g).toMonoidHom = rootGroup D c)
    (hPL : ∀ g ∈ P, L.map (MulAut.conj g).toMonoidHom = L) :
    ∃ L₂ ∈ rootLines D c \ {L}, ∀ g ∈ P, L₂.map (MulAut.conj g).toMonoidHom = L₂ := by
  have := hL.hyp.finite
  refine exists_map_conj_eq_of_isPGroup hP (fun g hg L' hL' => ⟨?_, fun h' => hL'.2 ?_⟩) ?_
  · exact map_conj_mem_rootLines_of_map_eq hL.hyp hL.closure hL.special hcD (hPc g hg) hL'.1
  · rw [Set.mem_singleton_iff] at h' ⊢
    exact Subgroup.map_injective (MulAut.conj g).injective (h'.trans (hPL g hg).symm)
  · obtain ⟨m, hm⟩ := hL.exists_ncard_rootLines hcD
    rw [Set.ncard_sdiff_singleton_of_mem hLc, hm, Nat.add_sub_cancel]
    exact not_dvd_two_pow hp.out hp2 m

theorem LineSetting.exists_mem_gatedPoints_fixed (hAll : AllLinesTI D) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {P : Subgroup G} (hP : IsPGroup p P) {a : G} (ha : a ∈ D) {T : Subgroup G}
    (hT : T ∈ rootLines D a)
    (hPa : ∀ g ∈ P, (rootGroup D a).map (MulAut.conj g).toMonoidHom = rootGroup D a)
    (hPT : ∀ g ∈ P, T.map (MulAut.conj g).toMonoidHom = T) :
    ∃ B ∈ gatedPoints D a T, ∀ g ∈ P, B.map (MulAut.conj g).toMonoidHom = B := by
  have h := hL.hyp
  have hc := hL.closure
  have hs := hL.special
  obtain ⟨_, ⟨⟨c, hcD, hcT, rfl⟩, hCa⟩, hCfix⟩ := hL.exists_fixed_linePoints hp2 hP ha hT hPa hPT
  have hTc := mem_rootLines_of_mem_rootLines h hc hs ha hT hcD hcT
  obtain ⟨L₂, ⟨hL₂, hL₂T⟩, hL₂fix⟩ := hL.exists_fixed_rootLines hp2 hP hcD hTc hCfix hPT
  obtain ⟨_, ⟨⟨e, heD, heL₂, rfl⟩, hEc⟩, hEfix⟩ :=
    hL.exists_fixed_linePoints hp2 hP hcD hL₂ hCfix hL₂fix
  have hL₂e := mem_rootLines_of_mem_rootLines h hc hs hcD hL₂ heD heL₂
  obtain ⟨L₃, ⟨hL₃, hL₃L₂⟩, hL₃fix⟩ := hL.exists_fixed_rootLines hp2 hP heD hL₂e hEfix hL₂fix
  obtain ⟨_, ⟨⟨x, hxD, hxL₃, rfl⟩, hBe⟩, hBfix⟩ :=
    hL.exists_fixed_linePoints hp2 hP heD hL₃ hEfix hL₃fix
  exact ⟨_, mem_gatedPoints_of_path h hc hs hL.conn hAll ha hcD heD hxD hT hcT hCa hL₂ hL₂T heL₂
    hEc hL₃ hL₃L₂ hxL₃ hBe, hBfix⟩

end Fixed

end CFSG.Timmesfeld.Bridge
