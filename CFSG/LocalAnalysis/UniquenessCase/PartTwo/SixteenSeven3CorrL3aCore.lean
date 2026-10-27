module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrL3aLin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrL3aFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrL3aAut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicOrderThreeAutomorphism

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

private lemma s16c167_exists_pair_ne_one_of_exp_two {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 4) (hexp : ∀ x : G, x * x = 1) :
    ∃ a b : G, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype G := Fintype.ofFinite G
  have hcard' : Fintype.card G = 4 := by rw [← Nat.card_eq_fintype_card, hcard]
  haveI : Nontrivial G :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [hcard']; norm_num)
  obtain ⟨a, ha⟩ : ∃ a : G, a ≠ 1 := exists_ne 1
  have hza : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers,
      orderOf_eq_prime (p := 2) (by simpa [pow_two] using hexp a) ha]
  have hlt : Subgroup.zpowers a < (⊤ : Subgroup G) := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hc : Nat.card (Subgroup.zpowers a) = Nat.card G := by rw [htop, Subgroup.card_top]
    rw [hza, hcard] at hc
    norm_num at hc
  obtain ⟨b, -, hbnot⟩ := SetLike.exists_of_lt hlt
  refine ⟨a, b, ha, ?_, ?_⟩
  · intro hb1
    exact hbnot (by rw [hb1]; exact Subgroup.one_mem _)
  · intro hba
    exact hbnot (by rw [← hba]; exact Subgroup.mem_zpowers a)

theorem s16c167_klein_pair {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ x : W, x * x = 1) (hcard : Nat.card W = 2 ^ 6) {L : Subgroup (MulAut W)}
    (hL : IsPOnePlusTwo 3 ↥L) {E : Subgroup (MulAut W)}
    (hEn : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hE : IsElemAbelian2 E)
    (hEcard : Nat.card E = 4) :
    ∃ z c d : MulAut W, z ∈ L ∧ z ≠ 1 ∧ (∀ y ∈ L, y * z = z * y) ∧ c ∈ E ∧ d ∈ E ∧
      c ≠ 1 ∧ c * z = z * c ∧ d * z = z⁻¹ * d := by
  classical
  haveI hExt : CFSG.IsExtraspecial 3 ↥L := hL.1
  have hZcard : Nat.card (Subgroup.center ↥L) = 3 :=
    CFSG.IsExtraspecial.center_order_p 3 ↥L
  haveI : Finite ↥(Subgroup.center ↥L) :=
    Nat.finite_of_card_ne_zero (by rw [hZcard]; norm_num)
  have hZne : Subgroup.center ↥L ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot (Subgroup.center ↥L)).mp (by rw [hZcard]; norm_num)
  obtain ⟨ℓ₀, hℓ01⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  set ℓ : ↥L := (ℓ₀ : ↥L) with hℓdef
  have hℓcen : ℓ ∈ Subgroup.center ↥L := ℓ₀.2
  have hℓ1 : ℓ ≠ 1 := by
    intro h
    exact hℓ01 (Subtype.ext h)
  set z : MulAut W := (ℓ : MulAut W) with hzdef
  have hzL : z ∈ L := ℓ.2
  have hz1 : z ≠ 1 := by
    intro h
    exact hℓ1 (Subtype.ext h)
  have hzc : ∀ y ∈ L, y * z = z * y := by
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hℓcen ⟨y, hy⟩)
  let κ : ↥E →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hEn)
  have hκ_apply : ∀ (t : ↥E) (x : ↥L),
      ((κ t) x : MulAut W) = (t : MulAut W) * (x : MulAut W) * (t : MulAut W)⁻¹ := by
    intro t x
    have h := Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hEn t) x
    rw [Subgroup.coe_inclusion] at h
    exact h
  have hκ_apply_z : ∀ t : ↥E,
      ((κ t) ℓ : MulAut W) = (t : MulAut W) * z * (t : MulAut W)⁻¹ := by
    intro t
    rw [hzdef]
    exact hκ_apply t ℓ
  let ρ : ↥E →* MulAut ↥(Subgroup.center ↥L) :=
    (MulAut.characteristic (Subgroup.center ↥L)).comp κ
  have hρ_apply : ∀ (t : ↥E) (x : ↥(Subgroup.center ↥L)),
      (((ρ t) x : ↥(Subgroup.center ↥L)) : ↥L) = (κ t) (x : ↥L) := by
    intro t x
    exact MulAut.characteristic_apply_apply_coe (Subgroup.center ↥L) (κ t) x
  have hρ_dich : ∀ t : ↥E, ρ t = 1 ∨
      ∀ x : ↥(Subgroup.center ↥L), (ρ t) x = x⁻¹ :=
    fun t => CFSG.GorensteinWalter.mulAut_eq_one_or_apply_eq_inv_of_card_eq_three hZcard (ρ t)
  have hρt1 : ∀ t : ↥E, (ρ t) ℓ₀ = ℓ₀ → κ t ℓ = ℓ := by
    intro t h
    have h2 := congrArg (fun x : ↥(Subgroup.center ↥L) => (x : ↥L)) h
    rw [hρ_apply t ℓ₀] at h2
    rw [hℓdef]
    exact h2
  have hκ_eq_one : ∀ t : ↥E, κ t = 1 → t = 1 := by
    intro t ht
    apply Subtype.ext
    apply s16c167_eq_one_of_commute_involution hW hcard hL
    · simpa [pow_two] using hE.2 (t : MulAut W) t.2
    · intro y hy
      have h1 : (κ t) ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [ht, MulAut.one_apply]
      have h2 : ((κ t) ⟨y, hy⟩ : MulAut W) = y := congrArg Subtype.val h1
      rw [hκ_apply t ⟨y, hy⟩] at h2
      calc (t : MulAut W) * y
          = ((t : MulAut W) * y * (t : MulAut W)⁻¹) * (t : MulAut W) := by group
        _ = y * (t : MulAut W) := by rw [h2]
  have hκ2 : ∀ t : ↥E, κ t * κ t = 1 := by
    intro t
    have htt : t * t = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hE.2 (t : MulAut W) t.2
    calc κ t * κ t = κ (t * t) := (map_mul κ t t).symm
      _ = κ 1 := by rw [htt]
      _ = 1 := map_one κ
  have hκcomm : ∀ s t : ↥E, κ s * κ t = κ t * κ s := by
    intro s t
    have hst : s * t = t * s := Subtype.ext (hE.1 (s : MulAut W) s.2 (t : MulAut W) t.2)
    calc κ s * κ t = κ (s * t) := (map_mul κ s t).symm
      _ = κ (t * s) := by rw [hst]
      _ = κ t * κ s := map_mul κ t s
  have hexpE : ∀ x : ↥E, x * x = 1 := by
    intro x
    apply Subtype.ext
    simpa [pow_two] using hE.2 (x : MulAut W) x.2
  obtain ⟨a, b, ha1, hb1, hab⟩ := s16c167_exists_pair_ne_one_of_exp_two hEcard hexpE
  have haa : a * a = 1 := hexpE a
  have hρ_ne_one : ρ ≠ 1 := by
    intro hρ1
    have hρt : ∀ t : ↥E, ρ t = 1 :=
      fun t => congrArg (fun f : ↥E →* MulAut ↥(Subgroup.center ↥L) => f t) hρ1
    have hfix : ∀ t : ↥E, ∀ x ∈ Subgroup.center ↥L, κ t x = x := by
      intro t x hx
      have h1 : (ρ t) ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hρt t, MulAut.one_apply]
      have h2 := congrArg (fun y : ↥(Subgroup.center ↥L) => (y : ↥L)) h1
      rw [hρ_apply t ⟨x, hx⟩] at h2
      exact h2
    have hκab : κ a = κ b :=
      s16c167_aut_eq_of_fix_center hL (hκ2 a) (hκ2 b) (hκcomm a b)
        (hfix a) (hfix b) (fun h => ha1 (hκ_eq_one a h)) (fun h => hb1 (hκ_eq_one b h))
    have hab1 : a * b = 1 := by
      apply hκ_eq_one (a * b)
      rw [map_mul, hκab, hκ2 b]
    have hba : b = a := by
      rw [eq_inv_of_mul_eq_one_right hab1, inv_eq_of_mul_eq_one_right haa]
    exact hab hba.symm
  obtain ⟨d, hd⟩ : ∃ d : ↥E, ρ d ≠ 1 := by
    by_contra h
    exact hρ_ne_one (MonoidHom.ext (fun t => not_not.mp (not_exists.mp h t)))
  have hd_inv : ∀ x : ↥(Subgroup.center ↥L), (ρ d) x = x⁻¹ := by
    rcases hρ_dich d with h | h
    · exact absurd h hd
    · exact h
  have hd_z : (d : MulAut W) * z = z⁻¹ * (d : MulAut W) := by
    have hκd : (κ d) ℓ = ℓ⁻¹ := by
      have h1 : (ρ d) ℓ₀ = ℓ₀⁻¹ := hd_inv ℓ₀
      have h2 := congrArg (fun x : ↥(Subgroup.center ↥L) => (x : ↥L)) h1
      rw [hρ_apply d ℓ₀, Subgroup.coe_inv, ← hℓdef] at h2
      exact h2
    have h3 : ((κ d) ℓ : MulAut W) = z⁻¹ := by
      rw [hκd, Subgroup.coe_inv, ← hzdef]
    rw [hκ_apply_z d] at h3
    calc (d : MulAut W) * z
        = ((d : MulAut W) * z * (d : MulAut W)⁻¹) * (d : MulAut W) := by group
      _ = z⁻¹ * (d : MulAut W) := by rw [h3]
  have hcomm_of_κ : ∀ t : ↥E, κ t ℓ = ℓ → (t : MulAut W) * z = z * (t : MulAut W) := by
    intro t ht
    have h3 : ((κ t) ℓ : MulAut W) = z := by rw [ht, ← hzdef]
    rw [hκ_apply_z t] at h3
    calc (t : MulAut W) * z
        = ((t : MulAut W) * z * (t : MulAut W)⁻¹) * (t : MulAut W) := by group
      _ = z * (t : MulAut W) := by rw [h3]
  have hc_exists : ∃ c : ↥E, c ≠ 1 ∧ κ c ℓ = ℓ := by
    have he : ∃ e : ↥E, e ≠ 1 ∧ e ≠ d := by
      by_cases hda : d = a
      · exact ⟨b, hb1, by rw [hda]; exact fun h => hab h.symm⟩
      · exact ⟨a, ha1, fun h => hda h.symm⟩
    obtain ⟨e, he1, hed⟩ := he
    rcases hρ_dich e with he_comm | he_inv
    · exact ⟨e, he1, hρt1 e (by rw [he_comm, MulAut.one_apply])⟩
    · refine ⟨e * d, ?_, ?_⟩
      · intro h1
        have hee : e * e = 1 := hexpE e
        have hde : d = e := by
          rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hee]
        exact hed hde.symm
      · apply hρt1
        rw [map_mul, MulAut.mul_apply, hd_inv ℓ₀, he_inv (ℓ₀⁻¹), inv_inv]
  obtain ⟨c, hc1, hc_comm⟩ := hc_exists
  exact ⟨z, (c : MulAut W), (d : MulAut W), hzL, hz1, hzc,
    c.2, d.2, (fun h => hc1 (Subtype.ext h)), hcomm_of_κ c hc_comm, hd_z⟩

theorem s16c167_codim_core {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ x : W, x * x = 1) (hcard : Nat.card W = 2 ^ 6) {L : Subgroup (MulAut W)}
    (hL : IsPOnePlusTwo 3 ↥L) {E : Subgroup (MulAut W)}
    (hEn : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hE : IsElemAbelian2 E)
    (hEcard : Nat.card E = 4) :
    (⨆ (t : MulAut W) (_ : t ∈ E ∧ t ≠ 1), fixV (Subgroup.zpowers t)).index ≤ 2 := by
  obtain ⟨z, c, d, hzL, hz1, hzc, hcE, hdE, hc1, hcz, hdz⟩ :=
    s16c167_klein_pair hW hcard hL hEn hE hEcard
  have hz3 : z * z * z = 1 := by
    have h := congrArg Subtype.val (hL.2.2 ⟨z, hzL⟩)
    simpa [pow_succ, mul_assoc] using h
  have hzcen : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g.1 g.2)
  have hzfix : ∀ x : W, z x = x → x = 1 := fun x hx =>
    s16c167_central_fixed_point_free hW hcard hL hzcen (fun h => hz1 (congrArg Subtype.val h)) hx
  have hc2 : c * c = 1 := by
    have h := hE.2 c hcE
    simpa [pow_two] using h
  have hd2 : d * d = 1 := by
    have h := hE.2 d hdE
    simpa [pow_two] using h
  have hd1 : d ≠ 1 := by
    intro hd
    rw [hd] at hdz
    have h1 : z = z⁻¹ := by simpa using hdz
    have h2 : z * z = 1 := by
      calc z * z = z * z⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel z
    have h3 : z = 1 := by
      calc z = z * z * z * (z * z)⁻¹ := by group
        _ = 1 := by rw [hz3, h2]; simp
    exact hz1 h3
  have h := s16c167_fixV_sup_index_le_two hW hcard hz3 hzfix hc2 hc1 hcz hd2 hdz
  refine le_trans (Subgroup.index_antitone ?_) h
  refine sup_le ?_ ?_
  · exact le_iSup₂_of_le c ⟨hcE, hc1⟩ le_rfl
  · exact le_iSup₂_of_le d ⟨hdE, hd1⟩ le_rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
