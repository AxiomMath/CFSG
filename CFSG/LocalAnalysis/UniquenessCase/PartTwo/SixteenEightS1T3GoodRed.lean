module

public import CFSG.Quasithin.Background.D36GluedL27

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

private theorem s16t3_good_odd_aux {W : Type*} [CommGroup W] {Z : Subgroup W} {y : MulAut W}
    {x : W} (hZ : ∀ z ∈ Z, y z = z) (hx : y x * x⁻¹ ∈ Z) (hx2 : x ^ 2 ∈ Z)
    {n : ℕ} (hn : Odd n) (hyn : y ^ n = 1) : y x = x := by
  set u : W := y x * x⁻¹ with hu
  have hyu : y u = u := hZ u hx
  have hyx : y x = u * x := by rw [hu]; group
  have hsq : u ^ 2 = 1 := by
    have h1 : y (x ^ 2) = x ^ 2 := hZ (x ^ 2) hx2
    rw [map_pow, hyx, mul_pow] at h1
    have h1' : u ^ 2 * x ^ 2 = 1 * x ^ 2 := by simpa using h1
    exact mul_right_cancel h1'
  have hk : ∀ k : ℕ, (y ^ k) x = x * u ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' y k, MulAut.mul_apply, ih, map_mul, map_pow, hyu, hyx, pow_succ' u k,
        mul_comm u x, mul_assoc]
  have h1 : x * u ^ n = x := by
    rw [← hk n, hyn]
    rfl
  have h2 : u ^ n = 1 := by simpa using h1
  obtain ⟨m, rfl⟩ := hn
  have h3 : u = 1 := by
    have : u ^ (2 * m + 1) = u := by
      rw [pow_succ, pow_mul, hsq, one_pow, one_mul]
    rw [← this]
    exact h2
  rw [hyx, h3, one_mul]

private theorem s16t3_model_modZ {W : Type} [CommGroup W] {D : FFModel}
    {L : Subgroup (MulAut W)} {I Z : Subgroup W} {π : D.Gam →* ↥L}
    (hπ : D.RealizesVia L I Z π)
    (Ffun : ↥D.sec → Subgroup D.Gam)
    (hFfix : ∀ (m : ↥D.sec) (γ : D.Gam), γ ∈ Ffun m →
      D.act γ (m : D.Amb) * (m : D.Amb)⁻¹ ∈ D.ker)
    {w : W} (hw : w ∈ I) :
    ∃ (m₀ : ↥D.sec) (P : Subgroup (MulAut W)),
      P ≤ L ∧ P = (Ffun m₀).map (L.subtype.comp π) ∧
      ∀ p ∈ P, p w * w⁻¹ ∈ Z := by
  obtain ⟨hπsurj, hZI, hkersec, hIU, hJZ, hsec, hker, β, hβsurj, hβker, hβeq⟩ := hπ
  obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (β ⟨w, hw⟩)
  let P : Subgroup (MulAut W) := (Ffun m₀).map (L.subtype.comp π)
  have hPL : P ≤ L := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x _
    exact (π x).2
  refine ⟨m₀, P, hPL, rfl, ?_⟩
  intro p hp
  rw [Subgroup.mem_map] at hp
  obtain ⟨γ, hγ, rfl⟩ := hp
  have hu : ((π γ : ↥L) : MulAut W) w ∈ I := hIU (π γ) w hw
  have hm : D.act γ (m₀ : D.Amb) ∈ D.sec := hsec γ (m₀ : D.Amb) m₀.2
  have hfix := hFfix m₀ γ hγ
  have heq1 := hβeq γ ⟨w, hw⟩ m₀ hu hm hm₀.symm
  have hmem : (D.act γ (m₀ : D.Amb))⁻¹ * (m₀ : D.Amb) ∈ D.ker := by
    have h := D.ker.inv_mem hfix
    rw [mul_inv_rev, inv_inv] at h
    rwa [mul_comm (m₀ : D.Amb) ((D.act γ (m₀ : D.Amb)))⁻¹] at h
  have hquot :
      QuotientGroup.mk (s := D.ker.subgroupOf D.sec) (⟨D.act γ (m₀ : D.Amb), hm⟩ : ↥D.sec) =
        QuotientGroup.mk (s := D.ker.subgroupOf D.sec) m₀ := by
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    simpa using hmem
  have heq2 : β ⟨((π γ : ↥L) : MulAut W) w, hu⟩ = β ⟨w, hw⟩ := by
    rw [heq1, hquot, hm₀]
  have hb1 : β (⟨((π γ : ↥L) : MulAut W) w, hu⟩ * ⟨w, hw⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, heq2, mul_inv_cancel]
  have huZ : ((π γ : ↥L) : MulAut W) w * w⁻¹ ∈ Z := by
    have := (hβker (⟨((π γ : ↥L) : MulAut W) w, hu⟩ * ⟨w, hw⟩⁻¹)).mp hb1
    simpa using this
  exact huZ

private theorem s16t3_model_w_sq_mem_Z {W : Type} [CommGroup W] {D : FFModel}
    {L : Subgroup (MulAut W)} {I Z : Subgroup W} {π : D.Gam →* ↥L}
    (hπ : D.RealizesVia L I Z π) (hsq : ∀ m ∈ D.sec, m * m ∈ D.ker)
    {w : W} (hw : w ∈ I) : w ^ 2 ∈ Z := by
  obtain ⟨hπsurj, hZI, hkersec, hIU, hJZ, hsec, hker, β, hβsurj, hβker, hβeq⟩ := hπ
  obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (β ⟨w, hw⟩)
  have hmemI : w ^ 2 ∈ I := I.pow_mem hw 2
  have hb : β ⟨w ^ 2, hmemI⟩ = 1 := by
    have hsub : (⟨w ^ 2, hmemI⟩ : ↥I) = ⟨w, hw⟩ ^ 2 := rfl
    rw [hsub, map_pow, ← hm₀]
    have hmemker : (m₀ * m₀ : ↥D.sec) ∈ D.ker.subgroupOf D.sec := by
      rw [Subgroup.mem_subgroupOf]
      exact hsq m₀ m₀.2
    have hq : QuotientGroup.mk (s := D.ker.subgroupOf D.sec) (m₀ * m₀) = 1 :=
      (QuotientGroup.eq_one_iff (N := D.ker.subgroupOf D.sec) (m₀ * m₀)).mpr hmemker
    have hpow : (QuotientGroup.mk (s := D.ker.subgroupOf D.sec) m₀) ^ 2 =
        QuotientGroup.mk (s := D.ker.subgroupOf D.sec) (m₀ * m₀) := by
      change ((QuotientGroup.mk' (D.ker.subgroupOf D.sec)) m₀) ^ 2 =
        (QuotientGroup.mk' (D.ker.subgroupOf D.sec)) (m₀ * m₀)
      rw [pow_two, map_mul]
    exact hpow.trans hq
  exact (hβker ⟨w ^ 2, hmemI⟩).mp hb

theorem s16t3_good_of_model {W : Type} [CommGroup W] [Finite W] {D : FFModel}
    {L : Subgroup (MulAut W)} {I Z : Subgroup W} {π : D.Gam →* ↥L}
    (hπ : D.RealizesVia L I Z π) (hfaith : D.Faithful)
    (hZ : ∀ l ∈ L, ∀ z ∈ Z, l z = z) (hsq : ∀ m ∈ D.sec, m * m ∈ D.ker)
    (hF : ∀ m ∈ D.sec, ∃ F : Subgroup D.Gam, IsPGroup 3 ↥F ∧ ¬ IsCyclic ↥F ∧
      ∀ γ ∈ F, D.act γ m * m⁻¹ ∈ D.ker)
    {w : W} (hw : w ∈ I) :
    ∃ E : Subgroup (MulAut W), E ≤ L ∧ IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E ∧ ∀ e ∈ E, e w = w := by
  have hπinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on hfaith hπ
  let Ffun : ↥D.sec → Subgroup D.Gam := fun m => Classical.choose (hF m m.2)
  have hFspec : ∀ m : ↥D.sec, IsPGroup 3 ↥(Ffun m) ∧ ¬ IsCyclic ↥(Ffun m) ∧
      ∀ γ ∈ Ffun m, D.act γ (m : D.Amb) * (m : D.Amb)⁻¹ ∈ D.ker :=
    fun m => Classical.choose_spec (hF m m.2)
  obtain ⟨m₀, E, hEL, hEeq, hEmod⟩ := s16t3_model_modZ hπ Ffun
    (fun m γ hγ => (hFspec m).2.2 γ hγ) hw
  rw [hEeq] at hEmod
  have hinj : Function.Injective (L.subtype.comp π) :=
    L.subtype_injective.comp hπinj
  have hEp : IsPGroup 3 ↥E := by
    rw [hEeq]
    exact (hFspec m₀).1.map (L.subtype.comp π)
  have hEnc : ¬ IsCyclic ↥E := by
    rw [hEeq]
    let e := Subgroup.equivMapOfInjective (Ffun m₀) (L.subtype.comp π) hinj
    intro hc
    exact (hFspec m₀).2.1 (isCyclic_of_surjective e.symm e.symm.surjective)
  have hw2Z : w ^ 2 ∈ Z := s16t3_model_w_sq_mem_Z hπ hsq hw
  refine ⟨E, hEL, hEp, hEnc, ?_⟩
  intro e he
  rw [hEeq] at he
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 he
  have hZy : ∀ z ∈ Z, ((π γ : ↥L) : MulAut W) z = z :=
    fun z hz => hZ (π γ) (π γ).2 z hz
  have huZ : ((π γ : ↥L) : MulAut W) w * w⁻¹ ∈ Z :=
    hEmod _ (Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩)
  obtain ⟨j, hj⟩ := (hFspec m₀).1 ⟨γ, hγ⟩
  have hyj : ((π γ : ↥L) : MulAut W) ^ (3 ^ j) = 1 := by
    have h1 : (π (⟨γ, hγ⟩ : ↥(Ffun m₀)) : ↥L) ^ (3 ^ j) = 1 := by
      have h := congrArg (π.comp (Ffun m₀).subtype) hj
      simpa using h
    have h2 : ((π (⟨γ, hγ⟩ : ↥(Ffun m₀)) : ↥L) : MulAut W) ^ (3 ^ j) = 1 := by
      simpa using congrArg (fun t : ↥L => (t : MulAut W)) h1
    rwa [show π (⟨γ, hγ⟩ : ↥(Ffun m₀)) = (π γ : ↥L) from rfl] at h2
  have hodd : Odd (3 ^ j) := (by decide : Odd 3).pow
  exact s16t3_good_odd_aux hZy huZ hw2Z hodd hyj

theorem s16t3_perfect_of_model {W : Type} [CommGroup W] [Finite W] {D : FFModel}
    {L : Subgroup (MulAut W)} {I Z : Subgroup W} {π : D.Gam →* ↥L}
    (hπ : D.RealizesVia L I Z π) (hfaith : D.Faithful)
    (hZ : ∀ l ∈ L, ∀ z ∈ Z, l z = z)
    (hF : ∀ m ∈ D.sec, ∃ F : Subgroup D.Gam, Group.IsPerfect ↥F ∧ 3 ∣ Nat.card ↥F ∧
      ∀ γ ∈ F, D.act γ m * m⁻¹ ∈ D.ker)
    {w : W} (hw : w ∈ I) :
    ∃ P : Subgroup (MulAut W), P ≤ L ∧ Group.IsPerfect P ∧ 3 ∣ Nat.card P ∧
      ∀ p ∈ P, p w = w := by
  have hπinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on hfaith hπ
  let Ffun : ↥D.sec → Subgroup D.Gam := fun m => Classical.choose (hF m m.2)
  have hFspec : ∀ m : ↥D.sec, Group.IsPerfect ↥(Ffun m) ∧ 3 ∣ Nat.card ↥(Ffun m) ∧
      ∀ γ ∈ Ffun m, D.act γ (m : D.Amb) * (m : D.Amb)⁻¹ ∈ D.ker :=
    fun m => Classical.choose_spec (hF m m.2)
  obtain ⟨m₀, P, hPL, hPeq, hPmod⟩ := s16t3_model_modZ hπ Ffun
    (fun m γ hγ => (hFspec m).2.2 γ hγ) hw
  have hinj : Function.Injective (L.subtype.comp π) :=
    L.subtype_injective.comp hπinj
  have hPperf : Group.IsPerfect ↥P := by
    rw [hPeq]
    let e := Subgroup.equivMapOfInjective (Ffun m₀) (L.subtype.comp π) hinj
    have : Group.IsPerfect ↥(Ffun m₀) := (hFspec m₀).1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hPcard : 3 ∣ Nat.card ↥P := by
    rw [hPeq, ← Nat.card_congr
      (Subgroup.equivMapOfInjective (Ffun m₀) (L.subtype.comp π) hinj).toEquiv]
    exact (hFspec m₀).2.1
  refine ⟨P, hPL, hPperf, hPcard, ?_⟩
  intro p hp
  exact CFSG.Quasithin.fixed_of_perfect hPperf.commutator_eq_top
    (fun z hz => mem_fixV.mpr (fun p hp => hZ p (hPL hp) z hz)) hPmod p hp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
