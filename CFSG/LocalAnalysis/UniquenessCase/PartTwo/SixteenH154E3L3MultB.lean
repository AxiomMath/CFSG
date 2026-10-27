module

public import CFSG.Quasithin.Recognition.St84.WeissB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3MultB1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Frame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

public theorem s16h_e3_exists_inner_of_odd_isL3 {Y : Type} [Group Y] [Finite Y] (h : IsL3 Y 1)
    (φ : MulAut Y) (hodd : Odd (orderOf φ)) :
    ∃ y : Y, ∀ z : Y, φ z = y * z * y⁻¹ := by
  haveI hs : IsSimpleGroup Y :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.isSimpleGroup_of_isL3 h
  let conj : Y →* MulAut Y := MulAut.conj
  have hker : conj.ker = Subgroup.center Y := by
    ext g
    constructor
    · intro hg
      rw [MonoidHom.mem_ker] at hg
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun (f : MulAut Y) => f z) hg
      have h1 : g * z * g⁻¹ = z := by simpa [conj, MulAut.conj_apply] using hz
      calc z * g = (g * z * g⁻¹) * g := by rw [h1]
        _ = g * z := by group
    · intro hg
      rw [MonoidHom.mem_ker]
      ext z
      rw [MulAut.conj_apply]
      have h2 : z * g = g * z := Subgroup.mem_center_iff.mp hg z
      calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [← h2]
        _ = z := by group
  have hkerbot : conj.ker = ⊥ := by
    rw [hker, CFSG.LocalAnalysis.UniquenessCase.PartTwo.center_eq_bot_of_isL3 h]
  have hinj : Function.Injective conj := (MonoidHom.ker_eq_bot_iff conj).mp hkerbot
  let N : Subgroup (MulAut Y) := conj.range
  have hNcard : Nat.card N = 168 := by
    change Nat.card conj.range = 168
    rw [← CFSG.LocalAnalysis.UniquenessCase.PartTwo.card_eq_of_isL3 h]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hidx : N.index = 2 := by
    have hmul := N.card_mul_index
    rw [CFSG.SeitzReduction.LinearPilot.card_mulAut_of_lieModel_PSL_three_two h, hNcard] at hmul
    omega
  have hNnormal : N.Normal := Subgroup.normal_of_index_eq_two hidx
  have hQcard : Nat.card (MulAut Y ⧸ N) = 2 := by
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hNcard, CFSG.SeitzReduction.LinearPilot.card_mulAut_of_lieModel_PSL_three_two h] at hq
    omega
  let π : MulAut Y →* MulAut Y ⧸ N := QuotientGroup.mk' N
  have hx2 : (π φ) ^ 2 = 1 := by
    rw [← hQcard]
    exact pow_card_eq_one'
  have hxord : (π φ) ^ orderOf φ = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hone : π φ = 1 := by
    have h2 : orderOf (π φ) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    have h3 : orderOf (π φ) ∣ orderOf φ := orderOf_dvd_iff_pow_eq_one.mpr hxord
    have hcop : Nat.Coprime 2 (orderOf φ) := hodd.coprime_two_left
    have hg : orderOf (π φ) ∣ Nat.gcd 2 (orderOf φ) := Nat.dvd_gcd h2 h3
    rw [hcop.gcd_eq_one] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  have hφN : φ ∈ N := by
    rw [← QuotientGroup.ker_mk' N]
    exact hone
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hφN
  exact ⟨y, fun z => by rw [← hy]; rfl⟩

@[instance_reducible] private noncomputable def s16h_e3_irrSetAction {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} (Y : Subgroup (MulAut W))
    (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    MulAction ↥Y ↥(irrSet L) where
  smul g I := ⟨(I : Subgroup W).map (g : MulAut W).toMonoidHom, by
    have hgm : L.map (MulAut.conj (g : MulAut W)).toMonoidHom = L :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hY g.2)
    have hgm' : L.map (MulAut.conj ((g : MulAut W)⁻¹)).toMonoidHom = L :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hY (Y.inv_mem g.2))
    exact CFSG.LocalAnalysis.WeakClosure81.map_mem_irrSet
      (fun x hx => by
        have hx' : MulAut.conj (g : MulAut W) x ∈
            L.map (MulAut.conj (g : MulAut W)).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hx
        rw [hgm] at hx'
        simpa [MulAut.conj_apply] using hx')
      (fun x hx => by
        have hx' : MulAut.conj ((g : MulAut W)⁻¹) x ∈
            L.map (MulAut.conj ((g : MulAut W)⁻¹)).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hx
        rw [hgm'] at hx'
        simpa [MulAut.conj_apply] using hx')
      I.2⟩
  one_smul I := Subtype.ext (by
    show (I : Subgroup W).map ((1 : ↥Y) : MulAut W).toMonoidHom = (I : Subgroup W)
    rw [Subgroup.coe_one]
    exact Subgroup.map_id (I : Subgroup W))
  mul_smul g h I := Subtype.ext (by
    show (I : Subgroup W).map (((g * h : ↥Y) : MulAut W)).toMonoidHom =
      ((I : Subgroup W).map (h : MulAut W).toMonoidHom).map (g : MulAut W).toMonoidHom
    rw [Subgroup.coe_mul, Subgroup.map_map]
    rfl)

private lemma s16h_e3_map_commSub_of_normalizes {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ L, g * x * g⁻¹ ∈ L) :
    ∀ u ∈ commSub (⊤ : Subgroup W) L, g u ∈ commSub (⊤ : Subgroup W) L := by
  intro u hu
  have h : commSub (⊤ : Subgroup W) L ≤
      Subgroup.comap g.toMonoidHom (commSub (⊤ : Subgroup W) L) := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, -, rfl⟩
    change g (x w * w⁻¹) ∈ commSub (⊤ : Subgroup W) L
    have hconj : g * x * g⁻¹ ∈ L := hg x hx
    have hgx : g (x w) = (g * x * g⁻¹) (g w) := by
      simp [MulAut.mul_apply, MulAut.conj_apply]
    rw [map_mul, map_inv, hgx]
    exact Subgroup.subset_closure ⟨g * x * g⁻¹, hconj, g w, trivial, rfl⟩
  exact h hu

private lemma s16h_e3_comm_sup_of {W : Type} [CommGroup W]
    {L L' : Subgroup (MulAut W)} {k : MulAut W}
    (hL : ∀ x ∈ L, k * x = x * k) (hL' : ∀ x ∈ L', k * x = x * k) :
    ∀ h : MulAut W, h ∈ (L ⊔ L' : Subgroup (MulAut W)) → k * h = h * k := by
  have hLC : L ≤ Subgroup.centralizer ({k} : Set (MulAut W)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hL x hx).symm
  have hL'C : L' ≤ Subgroup.centralizer ({k} : Set (MulAut W)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hL' x hx).symm
  have hC : (L ⊔ L' : Subgroup (MulAut W)) ≤ Subgroup.centralizer ({k} : Set (MulAut W)) :=
    sup_le hLC hL'C
  intro h hh
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hC hh)).symm

public theorem s16h_e3_l3_mult_seven_core {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    (hL : IsL3 ↥L 1) (C : s16h_L3Coord L U)
    (htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ X ⊓ normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom)
    (hcard : Nat.card ↥(irrSet L) = 7)
    (π : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))) →*
        GL (Fin 3) (ZMod 2))
    (hπ : ∀ (k : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))))
        (u : W) (hu : u ∈ U) (hku : (k : MulAut W) u ∈ U),
        C.ψ ⟨(k : MulAut W) u, hku⟩ = Multiplicative.ofAdd
          (Multiplicative.toAdd (C.ψ ⟨u, hu⟩) *
            (π k : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose)) :
    7 ∣ Nat.card ↥π.range := by
  classical
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun f g h => MulEquiv.ext (congrFun h))
  let K : Subgroup (MulAut W) :=
    X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))
  let Y : Subgroup (MulAut W) := X ⊓ normalizer (L : Set (MulAut W))
  have hKY : K ≤ Y := fun k hk =>
    ⟨hk.1, Subgroup.centralizer_le_normalizer (L : Set (MulAut W))
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hk.2)⟩
  have hYle : Y ≤ normalizer (L : Set (MulAut W)) := inf_le_right
  letI : MulAction ↥Y ↥(irrSet L) := s16h_e3_irrSetAction Y hYle
  haveI : Finite ↥Y := Subtype.finite
  haveI : Finite ↥(irrSet L) := Subtype.finite
  have htrans' : ∀ a b : ↥(irrSet L), ∃ h : ↥Y, h • a = b := by
    intro a b
    obtain ⟨g, hgY, hgmap⟩ := htrans a.1 a.2 b.1 b.2
    exact ⟨⟨g, hgY⟩, Subtype.ext hgmap.symm⟩
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let Q : Sylow 7 ↥Y := Classical.choice (inferInstance : Nonempty (Sylow 7 ↥Y))
  have hcardpow : Nat.card ↥(irrSet L) = 7 ^ 1 := by rw [hcard, pow_one]
  have htransQ : ∀ a b : ↥(irrSet L), ∃ g ∈ (Q : Subgroup ↥Y), g • a = b :=
    CFSG.Quasithin.St84.sylow_pretransitive_of_card_prime_pow_sylow (p := 7) (k := 1)
      hcardpow htrans' Q
  haveI : Fintype ↥(irrSet L) := Fintype.ofFinite _
  have hcardF : Fintype.card ↥(irrSet L) = 7 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := ↥(irrSet L))
    (by rw [hcardF]; norm_num)
  obtain ⟨c, hcQ, hcab⟩ := htransQ a b
  have hcact : (MulAction.toPermHom ↥Y ↥(irrSet L)) c ≠ 1 := by
    intro h1
    have h2 : c • a = a := by
      simpa [MulAction.toPermHom_apply, MulAction.toPerm_apply] using
        congrArg (fun e : Equiv.Perm ↥(irrSet L) => e a) h1
    rw [hcab] at h2
    exact hab h2.symm
  obtain ⟨m, hm⟩ := Q.isPGroup'.exists_card_eq
  have hordc_dvd : orderOf c ∣ 7 ^ m := by
    have h1 : orderOf (⟨c, hcQ⟩ : ↥(Q : Subgroup ↥Y)) ∣ Nat.card ↥(Q : Subgroup ↥Y) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rwa [hm] at h1
  obtain ⟨j, -, hordc⟩ := (Nat.dvd_prime_pow Nat.prime_seven).mp hordc_dvd
  have hordcW : orderOf ((c : ↥Y) : MulAut W) = orderOf c :=
    (Subgroup.orderOf_mk (c : MulAut W) c.2).symm
  have hordcW_dvd : orderOf ((c : ↥Y) : MulAut W) ∣ 7 ^ m := by
    rw [hordcW]; exact hordc_dvd
  have hcX : ((c : ↥Y) : MulAut W) ∈ X := c.2.1
  have hcNL : ((c : ↥Y) : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) := c.2.2
  let φL : MulAut ↥L := Subgroup.normalizerMonoidHom (H := L) ⟨(c : MulAut W), hcNL⟩
  have hφL : ∀ x : ↥L, ((φL x : ↥L) : MulAut W) =
      (c : MulAut W) * (x : MulAut W) * (c : MulAut W)⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨(c : MulAut W), hcNL⟩ x
  have hordφL : orderOf φL ∣ orderOf ((c : ↥Y) : MulAut W) := by
    have h1 : orderOf φL ∣ orderOf (⟨(c : MulAut W), hcNL⟩ :
        ↥(Subgroup.normalizer (L : Set (MulAut W)))) :=
      orderOf_map_dvd (Subgroup.normalizerMonoidHom (H := L)) ⟨(c : MulAut W), hcNL⟩
    rw [Subgroup.orderOf_mk] at h1
    exact h1
  have hoddφL : Odd (orderOf φL) := by
    obtain ⟨jL, -, hjL⟩ := (Nat.dvd_prime_pow Nat.prime_seven).mp (hordφL.trans hordcW_dvd)
    rw [hjL]; exact Odd.pow (by norm_num)
  obtain ⟨l₀, hl₀⟩ := s16h_e3_exists_inner_of_odd_isL3 hL φL hoddφL
  have hinnerL : ∀ x ∈ L, (c : MulAut W) * x * (c : MulAut W)⁻¹ =
      (l₀ : MulAut W) * x * (l₀ : MulAut W)⁻¹ := by
    intro x hx
    have h1 := hl₀ ⟨x, hx⟩
    have h2 : ((φL ⟨x, hx⟩ : ↥L) : MulAut W) =
        (((l₀ * ⟨x, hx⟩ * l₀⁻¹ : ↥L)) : MulAut W) := congrArg Subtype.val h1
    rw [hφL] at h2
    simpa using h2
  have hLmap_c : L.map (MulAut.conj (c : MulAut W)).toMonoidHom = L :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hcNL
  have hLne : L ≠ L' := by
    intro hEq
    have hcommL : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := fun x hx y hy =>
      F.comm x hx y (hEq ▸ hy)
    have htop : Subgroup.center ↥L = ⊤ := by
      apply le_antisymm le_top
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcommL (y : MulAut W) y.2 (x : MulAut W) x.2)
    have hbot : Subgroup.center ↥L = ⊥ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.center_eq_bot_of_isL3 hL
    have hcard1 : Nat.card ↥L = 1 := by
      rw [← Subgroup.card_top, ← htop, hbot, Subgroup.card_bot]
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.card_eq_of_isL3 hL] at hcard1
    norm_num at hcard1
  have hcNL' : ((c : ↥Y) : MulAut W) ∈ Subgroup.normalizer (L' : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rcases F.perm ((c : ↥Y) : MulAut W) hcX with ⟨-, hL'map, -, -⟩ | ⟨hLswap, -, -, -⟩
    · exact hL'map
    · exact absurd (hLmap_c.symm.trans hLswap) hLne
  obtain ⟨t, htT, hLt, -⟩ := F.swap
  have hLe : ↥L ≃* ↥L' :=
    (L.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).trans
      (MulEquiv.subgroupCongr hLt)
  have hL3' : IsL3 ↥L' 1 := CFSG.Blueprint.LieModel.of_mulEquiv hLe hL
  let φL' : MulAut ↥L' := Subgroup.normalizerMonoidHom (H := L') ⟨(c : MulAut W), hcNL'⟩
  have hφL' : ∀ x : ↥L', ((φL' x : ↥L') : MulAut W) =
      (c : MulAut W) * (x : MulAut W) * (c : MulAut W)⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L' ⟨(c : MulAut W), hcNL'⟩ x
  have hordφL' : orderOf φL' ∣ orderOf ((c : ↥Y) : MulAut W) := by
    have h1 : orderOf φL' ∣ orderOf (⟨(c : MulAut W), hcNL'⟩ :
        ↥(Subgroup.normalizer (L' : Set (MulAut W)))) :=
      orderOf_map_dvd (Subgroup.normalizerMonoidHom (H := L')) ⟨(c : MulAut W), hcNL'⟩
    rw [Subgroup.orderOf_mk] at h1
    exact h1
  have hoddφL' : Odd (orderOf φL') := by
    obtain ⟨jL', -, hjL'⟩ := (Nat.dvd_prime_pow Nat.prime_seven).mp (hordφL'.trans hordcW_dvd)
    rw [hjL']; exact Odd.pow (by norm_num)
  obtain ⟨l', hl'⟩ := s16h_e3_exists_inner_of_odd_isL3 hL3' φL' hoddφL'
  have hinnerL' : ∀ x ∈ L', (c : MulAut W) * x * (c : MulAut W)⁻¹ =
      (l' : MulAut W) * x * (l' : MulAut W)⁻¹ := by
    intro x hx
    have h1 := hl' ⟨x, hx⟩
    have h2 : ((φL' ⟨x, hx⟩ : ↥L') : MulAut W) =
        (((l' * ⟨x, hx⟩ * l'⁻¹ : ↥L')) : MulAut W) := congrArg Subtype.val h1
    rw [hφL'] at h2
    simpa using h2
  let k : MulAut W := (l' : MulAut W)⁻¹ * (l₀ : MulAut W)⁻¹ * (c : MulAut W)
  have hk_eq : (l₀ : MulAut W) * (l' : MulAut W) * k = (c : MulAut W) := by
    dsimp only [k]; group
  have hkX : k ∈ X := by
    have hl₀X : (l₀ : MulAut W) ∈ X := F.le_x l₀.2
    have hl'X : (l' : MulAut W) ∈ X := F.le_x' l'.2
    dsimp only [k]
    exact X.mul_mem (X.mul_mem (X.inv_mem hl'X) (X.inv_mem hl₀X)) hcX
  have hcL' : ∀ x ∈ L', (c : MulAut W) * x * (c : MulAut W)⁻¹ ∈ L' := by
    intro x hx
    have hmap : L'.map (MulAut.conj (c : MulAut W)).toMonoidHom = L' :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hcNL'
    have hx' : MulAut.conj (c : MulAut W) x ∈
        L'.map (MulAut.conj (c : MulAut W)).toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rw [hmap] at hx'
    simpa [MulAut.conj_apply] using hx'
  have hkcenL : ∀ x ∈ L, k * x = x * k := by
    intro x hx
    have hconj : k * x * k⁻¹ = x := by
      have h1 := hinnerL x hx
      have hl'x : (l' : MulAut W) * x = x * (l' : MulAut W) :=
        (F.comm x hx (l' : MulAut W) l'.2).symm
      calc k * x * k⁻¹
          = (l' : MulAut W)⁻¹ * ((l₀ : MulAut W)⁻¹ *
              ((c : MulAut W) * x * (c : MulAut W)⁻¹) * (l₀ : MulAut W)) *
              (l' : MulAut W) := by dsimp only [k]; group
        _ = (l' : MulAut W)⁻¹ * x * (l' : MulAut W) := by rw [h1]; group
        _ = x := by
            calc (l' : MulAut W)⁻¹ * x * (l' : MulAut W)
                = (l' : MulAut W)⁻¹ * (x * (l' : MulAut W)) := by group
              _ = (l' : MulAut W)⁻¹ * ((l' : MulAut W) * x) := by rw [hl'x]
              _ = x := by group
    calc k * x = (k * x * k⁻¹) * k := by group
      _ = x * k := by rw [hconj]
  have hkcenL' : ∀ x ∈ L', k * x = x * k := by
    intro x hx
    have hconj : k * x * k⁻¹ = x := by
      have h1 := hinnerL' x hx
      have hl₀x : (l₀ : MulAut W) * ((c : MulAut W) * x * (c : MulAut W)⁻¹) =
          ((c : MulAut W) * x * (c : MulAut W)⁻¹) * (l₀ : MulAut W) :=
        F.comm (l₀ : MulAut W) l₀.2 ((c : MulAut W) * x * (c : MulAut W)⁻¹) (hcL' x hx)
      have hl₀mid : (l₀ : MulAut W)⁻¹ * ((c : MulAut W) * x * (c : MulAut W)⁻¹) *
          (l₀ : MulAut W) = (c : MulAut W) * x * (c : MulAut W)⁻¹ := by
        rw [mul_assoc, ← hl₀x, ← mul_assoc, inv_mul_cancel, one_mul]
      calc k * x * k⁻¹
          = (l' : MulAut W)⁻¹ * ((l₀ : MulAut W)⁻¹ *
              ((c : MulAut W) * x * (c : MulAut W)⁻¹) * (l₀ : MulAut W)) *
              (l' : MulAut W) := by dsimp only [k]; group
        _ = (l' : MulAut W)⁻¹ * ((c : MulAut W) * x * (c : MulAut W)⁻¹) *
              (l' : MulAut W) := by rw [hl₀mid]
        _ = x := by rw [h1]; group
    calc k * x = (k * x * k⁻¹) * k := by group
      _ = x * k := by rw [hconj]
  have hkK : k ∈ K :=
    ⟨hkX, Subgroup.mem_centralizer_iff.mpr
      (fun h hh => (s16h_e3_comm_sup_of hkcenL hkcenL' h hh).symm)⟩
  have hUmap_of_mem : ∀ g ∈ K, U.map (g : MulAut W).toMonoidHom = U := by
    intro g hg
    have hgc : ∀ x ∈ L, g * x * g⁻¹ ∈ L := by
      intro x hx
      have hcomm : g * x = x * g :=
        (Subgroup.mem_centralizer_iff.mp hg.2 x (Subgroup.mem_sup_left hx)).symm
      have : g * x * g⁻¹ = x := by rw [hcomm]; group
      rw [this]; exact hx
    have hle : U.map (g : MulAut W).toMonoidHom ≤ U := by
      rw [Subgroup.map_le_iff_le_comap]
      intro u hu
      rw [Subgroup.mem_comap]
      have hgu : g u ∈ commSub (⊤ : Subgroup W) L :=
        s16h_e3_map_commSub_of_normalizes hgc u (F.u_eq ▸ hu)
      rw [← F.u_eq] at hgu
      exact hgu
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (f := (g : MulAut W).toMonoidHom) g.injective]
  have hI_le_U : ∀ I : ↥(irrSet L), (I : Subgroup W) ≤ U := by
    intro I
    calc (I : Subgroup W) = commSub (I : Subgroup W) L := (I.2.1).symm
      _ ≤ commSub (⊤ : Subgroup W) L := commSub_mono le_top le_rfl
      _ = U := F.u_eq.symm
  have hIk_le_U : ∀ I : ↥(irrSet L),
      (I : Subgroup W).map (k : MulAut W).toMonoidHom ≤ U := by
    intro I
    rw [← hUmap_of_mem k hkK]
    exact Subgroup.map_mono (hI_le_U I)
  have hstab_l₀ : ∀ H : Subgroup W, StableUnder L H →
      H.map (l₀ : MulAut W).toMonoidHom = H := by
    intro H hH
    apply le_antisymm
    · rintro x ⟨u, hu, rfl⟩
      simpa using hH (l₀ : MulAut W) l₀.2 u hu
    · intro x hx
      have hx' : (l₀ : MulAut W)⁻¹ x ∈ H :=
        hH ((l₀ : MulAut W)⁻¹) (L.inv_mem l₀.2) x hx
      have hmem := Subgroup.mem_map_of_mem ((l₀ : MulAut W).toMonoidHom) hx'
      simpa using hmem
  have hfix_l' : ∀ H : Subgroup W, H ≤ U → H.map (l' : MulAut W).toMonoidHom = H := by
    intro H hH
    apply le_antisymm
    · rintro x ⟨u, hu, rfl⟩
      change (l' : MulAut W) u ∈ H
      rw [F.fix_u (l' : MulAut W) l'.2 u (hH hu)]
      exact hu
    · intro x hx
      have hxx : (l' : MulAut W) x = x := F.fix_u (l' : MulAut W) l'.2 x (hH hx)
      exact ⟨x, hx, hxx⟩
  have hstab_kI : ∀ I : ↥(irrSet L), StableUnder L
      ((I : Subgroup W).map (k : MulAut W).toMonoidHom) := by
    intro I l hl u hu
    obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.mp hu
    have hcomm : (k : MulAut W) * l = l * (k : MulAut W) :=
      (Subgroup.mem_centralizer_iff.mp hkK.2 l (Subgroup.mem_sup_left hl)).symm
    exact ⟨l i, I.2.2.2.1 l hl i hi,
      by
        show (k * l) i = (l * k) i
        rw [hcomm]⟩
  have hact : ∀ I : ↥(irrSet L), c • I = (⟨k, hKY hkK⟩ : ↥Y) • I := by
    intro I
    apply Subtype.ext
    show (I : Subgroup W).map (c : MulAut W).toMonoidHom =
      (I : Subgroup W).map (k : MulAut W).toMonoidHom
    rw [show (c : MulAut W) = (l₀ : MulAut W) * (l' : MulAut W) * k from hk_eq.symm]
    have hcomp : ((l₀ : MulAut W) * (l' : MulAut W) * k).toMonoidHom =
        (l₀ : MulAut W).toMonoidHom.comp
          ((l' : MulAut W).toMonoidHom.comp (k : MulAut W).toMonoidHom) := by
      ext x; rfl
    rw [hcomp, ← Subgroup.map_map, ← Subgroup.map_map]
    rw [hfix_l' ((I : Subgroup W).map (k : MulAut W).toMonoidHom) (hIk_le_U I)]
    rw [hstab_l₀ ((I : Subgroup W).map (k : MulAut W).toMonoidHom) (hstab_kI I)]
  let α : ↥K →* Equiv.Perm ↥(irrSet L) :=
    (MulAction.toPermHom ↥Y ↥(irrSet L)).comp (Subgroup.inclusion hKY)
  have hαk_eq : α ⟨k, hkK⟩ = (MulAction.toPermHom ↥Y ↥(irrSet L)) c := by
    rw [show α ⟨k, hkK⟩ =
        (MulAction.toPermHom ↥Y ↥(irrSet L)) (⟨k, hKY hkK⟩ : ↥Y) from rfl]
    apply Equiv.Perm.ext
    intro I
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply,
      MulAction.toPermHom_apply, MulAction.toPerm_apply]
    exact (hact I).symm
  have hαk_ne : α ⟨k, hkK⟩ ≠ 1 := by
    rw [hαk_eq]
    exact hcact
  have hαk_dvd : orderOf (α ⟨k, hkK⟩) ∣ 7 ^ j := by
    rw [hαk_eq]
    have h1 : orderOf ((MulAction.toPermHom ↥Y ↥(irrSet L)) c) ∣ orderOf c :=
      orderOf_map_dvd _ c
    rwa [hordc] at h1
  have h7 : 7 ∣ Nat.card α.range := by
    have hmem : α ⟨k, hkK⟩ ∈ α.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h1 : orderOf (⟨α ⟨k, hkK⟩, hmem⟩ : α.range) ∣ Nat.card α.range :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    obtain ⟨j', -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_seven).mp hαk_dvd
    have hj'pos : 0 < j' := by
      rcases Nat.eq_zero_or_pos j' with h0 | hpos
      · exfalso
        rw [h0, pow_zero] at hj'
        exact hαk_ne (orderOf_eq_one_iff.mp hj')
      · exact hpos
    have hdvd7 : 7 ∣ 7 ^ j' := by
      exact pow_dvd_pow 7 (Nat.succ_le_of_lt hj'pos)
    rw [hj'] at h1
    exact hdvd7.trans h1
  have hπker : π.ker ≤ α.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [MonoidHom.mem_ker]
    apply Equiv.Perm.ext
    intro I
    change ((MulAction.toPermHom ↥Y ↥(irrSet L)) (Subgroup.inclusion hKY x)) I = I
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
    apply Subtype.ext
    show (I : Subgroup W).map ((x : MulAut W)).toMonoidHom = (I : Subgroup W)
    have hfixU : ∀ u ∈ U, (x : MulAut W) u = u := by
      intro u hu
      have hxu : (x : MulAut W) u ∈ U := by
        have hmem := Subgroup.mem_map_of_mem ((x : MulAut W).toMonoidHom) hu
        rwa [hUmap_of_mem (x : MulAut W) x.2] at hmem
      have hψ : C.ψ ⟨(x : MulAut W) u, hxu⟩ = C.ψ ⟨u, hu⟩ := by
        have h := hπ x u hu hxu
        rw [hx] at h
        simpa using h
      exact congrArg Subtype.val (C.ψ.injective hψ)
    apply le_antisymm
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
      change (x : MulAut W) u ∈ (I : Subgroup W)
      rw [hfixU u (hI_le_U I hu)]
      exact hu
    · intro v hv
      exact ⟨v, hv, hfixU v (hI_le_U I hv)⟩
  have hrange_dvd : Nat.card α.range ∣ Nat.card π.range := by
    rw [← Subgroup.index_ker α, ← Subgroup.index_ker π]
    exact Subgroup.index_dvd_of_le hπker
  exact h7.trans hrange_dvd

public theorem s16h_e3_l3_mult_seven_cycle {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    (hL : IsL3 ↥L 1) (C : s16h_L3Coord L U)
    (htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ X ⊓ normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom)
    (π : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))) →*
        GL (Fin 3) (ZMod 2))
    (hπ : ∀ (k : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))))
        (u : W) (hu : u ∈ U) (hku : (k : MulAut W) u ∈ U),
        C.ψ ⟨(k : MulAut W) u, hku⟩ = Multiplicative.ofAdd
          (Multiplicative.toAdd (C.ψ ⟨u, hu⟩) *
            (π k : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose)) :
    ∃ k : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))),
      orderOf (π k) = 7 := by
  have hcard : Nat.card ↥(irrSet L) = 7 := s16h_e3_irrSet_L3_card_seven_of_coord F.u_eq.symm C
  have h7 : 7 ∣ Nat.card ↥π.range :=
    s16h_e3_l3_mult_seven_core F hL C htrans hcard π hπ
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : Finite ↥π.range := Subtype.finite
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥π.range) 7 h7
  rw [Subgroup.orderOf_mk] at hxord
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp x.2
  exact ⟨k, by rw [hk]; exact hxord⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
