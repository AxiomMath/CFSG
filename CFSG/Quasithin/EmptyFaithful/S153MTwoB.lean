module

public import CFSG.Quasithin.EmptyFaithful.S153MTwoDef
import CFSG.Quasithin.EmptyFaithful.S153LKsA
import CFSG.Timmesfeld.Orders.Classical
import CFSG.LieType.Ree.SuzukiOrder
import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.EmptyFaithful.S153LKsDef
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace S153M

section Quad

variable {V : Type} [CommGroup V]

private theorem twoB56_commV_apply_mem {A B : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {b : MulAut V} (hb : b ∈ B) {u : V}
    (hu : u ∈ commV A) : b u ∈ commV A := by
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    have h1 : x (b v) = b (x v) := by
      have := congrArg (fun f : MulAut V => f v) (hcomm x hx b hb)
      simpa using this
    rw [map_mul, map_inv, ← h1]
    exact Subgroup.subset_closure ⟨x, hx, b v, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a c _ _ ha hc => rw [map_mul]; exact mul_mem ha hc
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

private theorem twoB56_commV_le_fixV {L₁ L₂ : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hperf : Group.IsPerfect ↥L₂)
    {C W₁ W₂ : Subgroup V} (hC : C ≤ fixV L₂) (hW₁ : commV L₁ ≤ W₁) (hW₂ : commV L₂ ≤ W₂)
    (hCW : W₁ ⊓ W₂ ≤ C) : commV L₁ ≤ fixV L₂ := by
  intro u hu
  have hmem : ∀ b ∈ L₂, (b : MulAut V) u * u⁻¹ ∈ C := by
    intro b hb
    refine hCW ⟨hW₁ ?_, hW₂ (Subgroup.subset_closure ⟨b, hb, u, rfl⟩)⟩
    exact mul_mem (twoB56_commV_apply_mem hcomm hb hu) (inv_mem hu)
  let f : ↥L₂ →* V :=
    { toFun := fun b => (b : MulAut V) u * u⁻¹
      map_one' := by simp
      map_mul' := fun b b' => by
        have hc : (b' : MulAut V) u * u⁻¹ ∈ fixV L₂ := hC (hmem b' b'.2)
        have h1 : (b : MulAut V) ((b' : MulAut V) u * u⁻¹) = (b' : MulAut V) u * u⁻¹ := hc b b.2
        rw [map_mul, map_inv] at h1
        have h2 : (b : MulAut V) ((b' : MulAut V) u) =
            (b' : MulAut V) u * u⁻¹ * (b : MulAut V) u := mul_inv_eq_iff_eq_mul.1 h1
        show ((b : MulAut V) * (b' : MulAut V)) u * u⁻¹ = _
        rw [MulAut.mul_apply, h2]
        ac_rfl }
  have hker : ∀ b : ↥L₂, f b = 1 := by
    intro b
    have : b ∈ commutator ↥L₂ := by rw [hperf.commutator_eq_top]; trivial
    exact MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker f this)
  intro b hb
  have := hker ⟨b, hb⟩
  exact mul_inv_eq_one.1 this

end Quad

section Conj

variable {V : Type} [CommGroup V]

private theorem twoB56_conj_apply (τ a : MulAut V) (v : V) :
    ((MulAut.conj τ).toMonoidHom a) v = τ (a (τ⁻¹ v)) := by
  simp [MulAut.conj_apply]

private theorem twoB56_commV_map {L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (hτ : L₂ = L₁.map (MulAut.conj τ).toMonoidHom) :
    (commV L₁).map τ.toMonoidHom = commV L₂ := by
  subst hτ
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨a, ha, v, rfl⟩
    show τ (a v * v⁻¹) ∈ commV _
    have : τ (a v * v⁻¹) = ((MulAut.conj τ).toMonoidHom a) (τ v) * (τ v)⁻¹ := by
      rw [twoB56_conj_apply, map_mul, map_inv]
      simp
    rw [this]
    exact Subgroup.subset_closure ⟨_, Subgroup.mem_map_of_mem _ ha, τ v, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨x, hx, v, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨a (τ⁻¹ v) * (τ⁻¹ v)⁻¹, Subgroup.subset_closure ⟨a, ha, τ⁻¹ v, rfl⟩, ?_⟩
    show τ (a (τ⁻¹ v) * (τ⁻¹ v)⁻¹) = _
    rw [twoB56_conj_apply, map_mul, map_inv]
    simp

end Conj

section Orders

private theorem twoB56_card_psl2 {Y : Type} [Group Y] {Ks : Subgroup Y}
    {n : ℕ} (hn : 0 < n) (h : IsPSL 2 2 n ↥Ks) :
    Nat.card ↥Ks = 2 ^ n * (2 ^ (2 * n) - 1) := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  rw [hc]
  have hg : Nat.gcd (1 + 1) (2 ^ n - 1) = 1 :=
    Nat.coprime_two_left.mpr (S153L.ks_odd_two_pow_sub_one hn)
  unfold CFSG.Open.ordA
  rw [show (2 : ℕ) - 1 = 1 from rfl, show Finset.Icc 2 (1 + 1) = {2} by decide,
    Finset.prod_singleton, hg, Nat.div_one, show 1 * (1 + 1) / 2 = 1 from rfl, pow_one, pow_mul']

private theorem twoB56_card_sz {Y : Type} [Group Y] {Ks : Subgroup Y}
    {n : ℕ} (h : IsSz n ↥Ks) :
    Nat.card ↥Ks = 2 ^ (2 * n) * (2 ^ (2 * n) + 1) * (2 ^ n - 1) := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hf]; exact hK
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK', ← hf]
  ring

private theorem twoB56_card_statedSL_two {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

private theorem twoB56_card_statedSL_three {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 3 F) = Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three F

private theorem twoB56_card_center_sl3 {K : Type} [Field K] [Finite K] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) = Nat.gcd (Nat.card K - 1) 3 := by
  have h : rootsOfUnity 3 K = (powMonoidHom 3 : Kˣ →* Kˣ).ker := by
    ext x
    rw [mem_rootsOfUnity, MonoidHom.mem_ker, powMonoidHom_apply]
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
    Fintype.card_fin, h, IsCyclic.card_powMonoidHom_ker, Nat.card_units]

private theorem twoB56_card_center_dvd {Λ F : Type} [Group Λ] [Field F] [Finite F]
    (e : Λ ≃* ↥(StatedSL 3 F)) : Nat.card (Subgroup.center Λ) ∣ 3 := by
  have h1 : Nat.card (Subgroup.center Λ) = Nat.card (Subgroup.center ↥(StatedSL 3 F)) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  have h2 : Nat.card (Subgroup.center ↥(StatedSL 3 F)) =
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) :=
    (Nat.card_congr (Subgroup.centerCongr (specialLinearGroupEquivStatedSL 3 F)).toEquiv).symm
  rw [h1, h2, twoB56_card_center_sl3]
  exact Nat.gcd_dvd_right _ _

private theorem twoB56_card_statedSL_three_two {K : Type} [Field K] [Finite K] (h : Nat.card K = 2) :
    Nat.card ↥(StatedSL 3 K) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two h

end Orders

section Arith

private theorem twoB56_two_pow_mul_odd_inj {a b u w : ℕ} (hu : Odd u) (hw : Odd w)
    (h : 2 ^ a * u = 2 ^ b * w) : a = b := by
  have hu' : ¬ 2 ∣ u := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hu
  have hw' : ¬ 2 ∣ w := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hw
  have h1 : padicValNat 2 (2 ^ a * u) = a := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hu.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hu', add_zero]
  have h2 : padicValNat 2 (2 ^ b * w) = b := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hw.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hw', add_zero]
  rw [← h1, ← h2, h]

private theorem twoB56_odd_mul_c {c u : ℕ} (hc : c = 1 ∨ c = 3) (hu : Odd u) : Odd (c * u) := by
  rcases hc with rfl | rfl
  · simpa using hu
  · exact Odd.mul (by decide) hu

private theorem twoB56_odd_two_pow_add_one {k : ℕ} (hk : 0 < k) : Odd (2 ^ k + 1) :=
  ((Nat.even_pow' hk.ne').mpr even_two).add_one

private theorem twoB56_arith_psl2 {m n c : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hc : c = 1 ∨ c = 3)
    (h : 2 ^ n * (2 ^ (2 * n) - 1) * c =
      2 ^ (3 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1))) : False := by
  have hu : Odd ((2 ^ (2 * n) - 1) * c) := by
    rw [mul_comm]
    exact twoB56_odd_mul_c hc (S153L.ks_odd_two_pow_sub_one (by omega))
  have hw : Odd ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1)) :=
    (S153L.ks_odd_two_pow_sub_one (by omega)).mul (S153L.ks_odd_two_pow_sub_one (by omega))
  have h' : 2 ^ n * ((2 ^ (2 * n) - 1) * c) =
      2 ^ (3 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1)) := by rw [← h]; ring
  have hn3 : n = 3 * m := twoB56_two_pow_mul_odd_inj hu hw h'
  subst hn3
  have hpos : 0 < 2 ^ (3 * m) := by positivity
  have h2 : (2 ^ (2 * (3 * m)) - 1) * c = (2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc 2 ^ (3 * m) * ((2 ^ (2 * (3 * m)) - 1) * c) = 2 ^ (3 * m) * (2 ^ (2 * (3 * m)) - 1) * c := by ring
      _ = _ := h
      _ = _ := by ring
  have hx : 2 ^ (2 * (3 * m)) = 2 ^ (3 * m) * 2 ^ (3 * m) := by rw [← pow_add]; congr 1; omega
  have hxy : 2 ^ (2 * m) ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hx2 : 2 ≤ 2 ^ (3 * m) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hy1 : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
  rw [hx] at h2
  generalize 2 ^ (3 * m) = x at *
  generalize 2 ^ (2 * m) = y at *
  have hc1 : 1 ≤ c := by rcases hc with rfl | rfl <;> norm_num
  have h3 : (y - 1) * (x - 1) ≤ (x - 1) * (x - 1) := Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hxy 1)
  have h4 : (x - 1) * (x - 1) < x * x - 1 := by
    obtain ⟨z, rfl⟩ : ∃ z, x = z + 2 := ⟨x - 2, by omega⟩
    have e1 : z + 2 - 1 = z + 1 := by omega
    have e2 : (z + 2) * (z + 2) - 1 = z * z + 4 * z + 3 := by
      have : (z + 2) * (z + 2) = z * z + 4 * z + 4 := by ring
      omega
    rw [e1, e2]
    nlinarith
  have h5 : x * x - 1 ≤ (x * x - 1) * c := Nat.le_mul_of_pos_right _ hc1
  omega

private theorem twoB56_arith_sz {m n c : ℕ} (hm : 1 ≤ m) (hn : 3 ≤ n) (hc : c = 1 ∨ c = 3)
    (h : 2 ^ (2 * n) * (2 ^ (2 * n) + 1) * (2 ^ n - 1) * c =
      2 ^ (3 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1))) : False := by
  have hu : Odd (c * ((2 ^ (2 * n) + 1) * (2 ^ n - 1))) :=
    twoB56_odd_mul_c hc ((twoB56_odd_two_pow_add_one (by omega)).mul
      (S153L.ks_odd_two_pow_sub_one (by omega)))
  have hw : Odd ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1)) :=
    (S153L.ks_odd_two_pow_sub_one (by omega)).mul (S153L.ks_odd_two_pow_sub_one (by omega))
  have h' : 2 ^ (2 * n) * (c * ((2 ^ (2 * n) + 1) * (2 ^ n - 1))) =
      2 ^ (3 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1)) := by rw [← h]; ring
  have h23 : 2 * n = 3 * m := twoB56_two_pow_mul_odd_inj hu hw h'
  obtain ⟨k, hk1, hk2⟩ : ∃ k, n = 3 * k ∧ m = 2 * k := ⟨n / 3, by omega, by omega⟩
  subst hk1 hk2
  have hk : 1 ≤ k := by omega
  have e1 : 2 ^ (2 * (3 * k)) = (2 ^ k) ^ 6 := by rw [← pow_mul]; congr 1; ring
  have e2 : 2 ^ (3 * k) = (2 ^ k) ^ 3 := by rw [← pow_mul]; congr 1; ring
  have e3 : 2 ^ (3 * (2 * k)) = (2 ^ k) ^ 6 := by rw [← pow_mul]; congr 1; ring
  have e4 : 2 ^ (2 * (2 * k)) = (2 ^ k) ^ 4 := by rw [← pow_mul]; congr 1; ring
  rw [e1, e2, e3, e4] at h
  have ht2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have ht1 : 1 ≤ 2 ^ k := by omega
  generalize hT : 2 ^ k = t at *
  have ht3 : 1 ≤ t ^ 3 := Nat.one_le_pow _ _ (by omega)
  have ht3' : 2 ≤ t ^ 3 := by
    calc 2 ≤ t := ht2
      _ ≤ t ^ 3 := Nat.le_self_pow (by norm_num) t
  have ht6 : t ^ 6 = t ^ 3 * t ^ 3 := by rw [← pow_add]
  have ht4 : 1 ≤ t ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hfac : t ^ 6 - 1 = (t ^ 3 - 1) * (t ^ 3 + 1) := by
    rw [ht6, mul_comm (t ^ 3 - 1)]
    have := Nat.mul_self_sub_mul_self_eq (t ^ 3) 1
    simpa using this
  rw [hfac] at h
  have hpos : 0 < t ^ 6 * (t ^ 3 - 1) := by
    have : 0 < t ^ 3 - 1 := by omega
    positivity
  have h2 : (t ^ 6 + 1) * c = (t ^ 4 - 1) * (t ^ 3 + 1) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc t ^ 6 * (t ^ 3 - 1) * ((t ^ 6 + 1) * c)
        = t ^ 6 * (t ^ 6 + 1) * (t ^ 3 - 1) * c := by ring
      _ = t ^ 6 * ((t ^ 4 - 1) * ((t ^ 3 - 1) * (t ^ 3 + 1))) := h
      _ = _ := by ring
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    obtain rfl : t = 2 := by rw [← hT]; norm_num
    rcases hc with rfl | rfl <;> norm_num at h2
  · have ht4' : 4 ≤ t := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        _ = t := hT
    have hu4 : 4 * t ^ 3 ≤ t ^ 4 := by
      calc 4 * t ^ 3 ≤ t * t ^ 3 := Nat.mul_le_mul_right _ ht4'
        _ = t ^ 4 := by ring
    have hu64 : 64 ≤ t ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ t ^ 3 := Nat.pow_le_pow_left ht4' 3
    rw [ht6] at h2
    generalize t ^ 3 = u at *
    generalize t ^ 4 = w at *
    zify [ht4] at h2
    have hw1 : 1 ≤ w := by omega
    have hwz : (4 : ℤ) * u ≤ w := by exact_mod_cast hu4
    have huz : (64 : ℤ) ≤ u := by exact_mod_cast hu64
    rcases hc with rfl | rfl
    · push_cast at h2
      nlinarith [mul_nonneg (sub_nonneg.2 hwz) (by positivity : (0 : ℤ) ≤ u + 1)]
    · push_cast at h2
      nlinarith [mul_nonneg (sub_nonneg.2 hwz) (by positivity : (0 : ℤ) ≤ u + 1)]

end Arith

section Excl

private theorem twoB56_injective_of_faithful {V : Type} [CommGroup V] {D : FFModel}
    (hD : D.Faithful) {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) : Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨-, -, -, hHU, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  apply hD
  intro m hm
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
  have hact : D.act γ m ∈ D.sec := hsec γ m hm
  have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hHU (π γ) u u.2
  have h1 := hβe γ u ⟨m, hm⟩ hu' hact hu
  have h2' : ((π γ : ↥H) : MulAut V) (u : V) = (u : V) := by rw [hγ]; rfl
  have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) = u := Subtype.ext h2'
  rw [h2, hu] at h1
  have h3 := QuotientGroup.eq.mp h1
  have h4 : m⁻¹ * D.act γ m ∈ D.ker := h3
  rw [mul_comm]
  exact h4

private theorem twoB56_bijective {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {ι : Type}
    [Fintype ι] [DecidableEq ι] {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    {U Z : Subgroup V} {π : ↥Γ →* ↥L} (h : (FFModel.nat Γ).RealizesVia L U Z π) :
    Function.Bijective π :=
  ⟨twoB56_injective_of_faithful (FFModel.nat_faithful Γ) h, h.1⟩

private theorem twoB56_ksCoverTwo_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : KsCoverTwo L) : KsCoverTwo L' := by
  obtain ⟨Y, _, Ks, n, σ, h3, hodd, hKs, hs, hz⟩ := h
  refine ⟨Y, inferInstance, Ks, n, σ.comp e.symm.toMonoidHom, h3, hodd, hKs,
    hs.comp e.symm.surjective, ?_⟩
  intro x hx
  have hx' : e.symm x ∈ σ.ker := hx
  have := hz hx'
  rw [Subgroup.mem_center_iff] at this ⊢
  intro g
  have h1 := this (e.symm g)
  have h2 := congrArg e h1
  simpa using h2

private theorem twoB56_card_ge {L : Type} [Group L] [Finite L]
    (hK : KsCoverTwo L) : 504 ≤ Nat.card L := by
  obtain ⟨Y, _, Ks, n, σ, hn3, hodd, hshape, hs, hz⟩ := hK
  have hK' : S153L.KsCover L :=
    ⟨Y, inferInstance, Ks, n, σ, hn3, hodd, hshape.elim Or.inl fun h => Or.inr (Or.inl h), hs, hz⟩
  obtain ⟨N, hN, hcard⟩ := hK'.card_data_eq
  have hpos : 0 < Nat.card ↥(Subgroup.center L) := Nat.card_pos
  rw [hcard]
  exact (S153L.ksOrd_ge hN).trans (Nat.le_mul_of_pos_right _ hpos)

private theorem twoB56_sl3_false {L : Type} [Group L] [Finite L]
    (hK : KsCoverTwo L) {F : Type} [Field F] [Finite F] {m : ℕ} (hm : Nat.card F = 2 ^ m)
    (e : ↥(StatedSL 3 F) ≃* L) : False := by
  obtain ⟨Y, _, Ks, n, σ, hn3, hodd, hshape, hs, hz⟩ := hK
  have hm1 : 1 ≤ m := by
    by_contra h0
    obtain rfl : m = 0 := by omega
    have h1 := Finite.one_lt_card (α := F)
    rw [pow_zero] at hm
    omega
  have hcardL : Nat.card L = Nat.card ↥Ks * Nat.card ↥σ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective σ hs).toEquiv]
  have hZ : Nat.card ↥σ.ker ∣ 3 :=
    (Subgroup.card_dvd_of_le hz).trans (twoB56_card_center_dvd e.symm)
  have hc : Nat.card ↥σ.ker = 1 ∨ Nat.card ↥σ.ker = 3 := (Nat.dvd_prime Nat.prime_three).1 hZ
  have hLc : Nat.card L = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
    rw [← Nat.card_congr e.toEquiv, twoB56_card_statedSL_three, hm]
  have e3 : (2 : ℕ) ^ (3 * m) = (2 ^ m) ^ 3 := pow_mul' 2 3 m
  have e2 : (2 : ℕ) ^ (2 * m) = (2 ^ m) ^ 2 := pow_mul' 2 2 m
  rcases hshape with h | h
  · have hKs := twoB56_card_psl2 (by omega) h
    refine twoB56_arith_psl2 (n := n) hm1 (by omega) hc ?_
    rw [← hKs, ← hcardL, hLc, e3, e2]
  · have hKs := twoB56_card_sz h
    refine twoB56_arith_sz (n := n) hm1 hn3 hc ?_
    rw [← hKs, ← hcardL, hLc, e3, e2]

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)}

private theorem twoB56_false_of_sl3 (hK : KsCoverTwo ↥L) {F : Type}
    [Field F] [Finite F] {m : ℕ} (hm : Nat.card F = 2 ^ m) {U Z : Subgroup V}
    (h : (FFModel.nat (StatedSL 3 F)).Realizes L U Z) : False := by
  obtain ⟨π, hπ⟩ := h
  exact twoB56_sl3_false hK hm (MulEquiv.ofBijective π (twoB56_bijective hπ))

private theorem twoB56_two_le (hK : KsCoverTwo ↥L) {F : Type}
    [Field F] [Finite F] {m : ℕ} (hm : Nat.card F = 2 ^ m) {U Z : Subgroup V}
    (h : (FFModel.nat (StatedSL 2 F)).Realizes L U Z) : 2 ≤ m := by
  by_contra hlt
  obtain ⟨π, hπ⟩ := h
  have h1 := Finite.one_lt_card (α := F)
  have hm2 : m < 2 := by omega
  interval_cases m
  · rw [pow_zero] at hm
    omega
  · have hF : Nat.card F = 2 := by simpa using hm
    have hc : Nat.card ↥L = 6 := by
      rw [← Nat.card_congr (Equiv.ofBijective π (twoB56_bijective hπ))]
      show Nat.card ↥(StatedSL 2 F) = 6
      rw [twoB56_card_statedSL_two, hF]
      norm_num
    have := twoB56_card_ge hK
    omega

private theorem twoB56_sym5_false (hK : KsCoverTwo ↥L)
    {U Z : Subgroup V} (h : SymmetricNatural L U Z 5) : False := by
  obtain ⟨π, hπ⟩ := h
  have h1 : Nat.card ↥L ≤ Nat.card (Equiv.Perm (Fin 5)) := Nat.card_le_card_of_surjective π hπ.1
  have h2 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have := twoB56_card_ge hK
  omega

private theorem twoB56_sl3two_false (hK : KsCoverTwo ↥L)
    (e : Nonempty (↥L ≃* ↥(StatedSL 3 (ZMod 2)))) : False := by
  obtain ⟨e⟩ := e
  have h1 : Nat.card ↥L = 168 := by
    rw [Nat.card_congr e.toEquiv]
    exact twoB56_card_statedSL_three_two (Nat.card_zmod 2)
  have := twoB56_card_ge hK
  omega

private theorem twoB56_piece {W C : Subgroup V} (hK : KsCoverTwo ↥L)
    (h : B56Piece L W C) :
    W = commV L ⊔ C ∧ ∃ m, 2 ≤ m ∧ BinaryNaturalSL L (commV L ⊔ C) C 2 m := by
  rcases h with ⟨hW, h⟩ | ⟨hW, m, F, hF, hFin, hm, hd⟩ | ⟨e, -, -, -, -⟩
  · subst hW
    refine ⟨rfl, ?_⟩
    rcases h with ⟨n, F, hF, hFin, hn, hR⟩ | hS | ⟨m, F, hF, hFin, hm, hR⟩
    · exact ⟨n, twoB56_two_le hK hn hR, F, hF, hFin, hn, hR⟩
    · exact (twoB56_sym5_false hK hS).elim
    · exact (twoB56_false_of_sl3 hK hm hR).elim
  · obtain ⟨I, π, -, -, -, hreal⟩ := hd
    exact (twoB56_false_of_sl3 hK hm ⟨π, hreal ⟨0, by norm_num⟩⟩).elim
  · exact (twoB56_sl3two_false hK e).elim

end Excl

section Main

theorem twoNat_of_twoB56 {V : Type} [CommGroup V] [Finite V]
    {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (_hτX : τ ∈ X) (_hL₁X : L₁ ≤ X) (_hL₂X : L₂ ≤ X) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hτ : L₂ = L₁.map (MulAut.conj τ).toMonoidHom)
    (_hn : ∀ x ∈ X, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hK : KsCoverTwo ↥L₁) (h : TwoB56 X L₁ L₂) :
    TwoNat L₁ L₂ τ := by
  obtain ⟨-, W₁, W₂, -, -, hsup, hinf, hp₁, hp₂⟩ := h
  let e : ↥L₁ ≃* ↥L₂ :=
    (Subgroup.equivMapOfInjective L₁ (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective).trans
      (MulEquiv.subgroupCongr hτ.symm)
  have hK₂ : KsCoverTwo ↥L₂ := twoB56_ksCoverTwo_of_mulEquiv e hK
  have hperf₁ : Group.IsPerfect ↥L₁ := hq₁.1
  have hperf₂ : Group.IsPerfect ↥L₂ := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨hW₁, hn₁⟩ := twoB56_piece hK hp₁
  obtain ⟨hW₂, hn₂⟩ := twoB56_piece hK₂ hp₂
  have hc₁ : commV L₁ ≤ W₁ := hW₁ ▸ le_sup_left
  have hc₂ : commV L₂ ≤ W₂ := hW₂ ▸ le_sup_left
  have hcomm' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hfix₂ : fixV (L₁ ⊔ L₂) ≤ fixV L₂ := fun v hv x hx => hv x (Subgroup.mem_sup_right hx)
  have hfix₁ : fixV (L₁ ⊔ L₂) ≤ fixV L₁ := fun v hv x hx => hv x (Subgroup.mem_sup_left hx)
  have hq₂ : commV L₁ ≤ fixV L₂ := twoB56_commV_le_fixV hcomm hperf₂ hfix₂ hc₁ hc₂ hinf.le
  have hq₁' : commV L₂ ≤ fixV L₁ :=
    twoB56_commV_le_fixV hcomm' hperf₁ hfix₁ hc₂ hc₁ (by rw [inf_comm]; exact hinf.le)
  have hmap := twoB56_commV_map hτ
  unfold TwoNat
  refine ⟨hn₁, hn₂, ?_, ?_, ?_, hq₂, hq₁'⟩
  · rw [← hW₁, ← hW₂, hsup]
  · rw [← hW₁, ← hW₂, hinf]
  · have hsum : commV L₁ ⊔ commV L₂ ⊔ fixV (L₁ ⊔ L₂) = ⊤ := by
      rw [← hsup, hW₁, hW₂]
      ac_rfl
    unfold IsSumMod
    rw [hmap]
    exact ⟨hsum.symm, by rw [← hW₁, ← hW₂, hinf]⟩

end Main

end S153M

end CFSG.Quasithin
