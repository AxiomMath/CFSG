module

public import CFSG.Quasithin.Recognition.F112Crit.Theorem723
public import CFSG.Quasithin.Recognition.F112Crit.Theorem75

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise IsMulCommutative

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

theorem comm_of_conj_eq_self {t d : G} (e : t * d * t⁻¹ = d) : t * d = d * t := by
  calc t * d = t * d * t⁻¹ * t := by group
    _ = d * t := by rw [e]

theorem conj_mul_pair_eq {t z a b : G} (hz : t * z * t⁻¹ = z) (ha : t * a * t⁻¹ = b)
    (hb : t * b * t⁻¹ = a) (hab : a * b = b * a) : t * (z * (a * b)) * t⁻¹ = z * (a * b) := by
  calc t * (z * (a * b)) * t⁻¹ = (t * z * t⁻¹) * ((t * a * t⁻¹) * (t * b * t⁻¹)) := by group
    _ = z * (b * a) := by rw [hz, ha, hb]
    _ = z * (a * b) := by rw [hab]

theorem card_zpowers_le_two_of_sq {y : G} (hy : y ^ 2 = 1) :
    Nat.card (Subgroup.zpowers y) ≤ 2 := by
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hy)

theorem conj_swap_of_inv {V N : Subgroup G} (hN : N ≤ Subgroup.centralizer (V : Set G))
    {x z s : G} (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hx3 : x ^ 3 ∈ N) (hz : z ∈ V)
    (hsz : s * z * s⁻¹ = z) (hsx : s * x * s⁻¹ * x ∈ N) :
    s * (x * z * x⁻¹) * s⁻¹ = x ^ 2 * z * (x ^ 2)⁻¹ ∧
      s * (x ^ 2 * z * (x ^ 2)⁻¹) * s⁻¹ = x * z * x⁻¹ := by
  have hc : ∀ n ∈ N, ∀ a ∈ V, n * a * n⁻¹ = a := fun n hn a ha => by
    have h := Subgroup.mem_centralizer_iff.mp (hN hn) a ha
    rw [← h, mul_inv_cancel_right]
  have hzi : x⁻¹ * z * x ∈ V := ConjAut.conj_inv_mem V hxV hz
  have h2 : x ^ 2 * z * (x ^ 2)⁻¹ = x⁻¹ * z * x := by
    have h3 := hc _ hx3 z hz
    calc x ^ 2 * z * (x ^ 2)⁻¹ = x⁻¹ * (x ^ 3 * z * (x ^ 3)⁻¹) * x := by group
      _ = x⁻¹ * z * x := by rw [h3]
  obtain ⟨n, hn⟩ : ∃ n, s * x * s⁻¹ * x = n := ⟨_, rfl⟩
  rw [hn] at hsx
  have e1 : s * (x * z * x⁻¹) * s⁻¹ = n * (x⁻¹ * (s * z * s⁻¹) * x) * n⁻¹ := by
    rw [← hn]; group
  have e2 : s * (x⁻¹ * z * x) * s⁻¹ = x * (n⁻¹ * (s * z * s⁻¹) * n) * x⁻¹ := by
    rw [← hn]; group
  have hn' : n⁻¹ * z * n = z := by
    have := hc _ (N.inv_mem hsx) z hz
    rwa [inv_inv] at this
  refine ⟨?_, ?_⟩
  · rw [e1, hsz, hc n hsx _ hzi, h2]
  · rw [h2, e2, hsz, hn']

theorem conj_orbitProd_eq {V N : Subgroup G} [IsMulCommutative ↥V]
    (hN : N ≤ Subgroup.centralizer (V : Set G)) {x z : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hx3 : x ^ 3 ∈ N) (hz : z ∈ V) :
    x * (z * ((x * z * x⁻¹) * (x ^ 2 * z * (x ^ 2)⁻¹))) * x⁻¹ =
      z * ((x * z * x⁻¹) * (x ^ 2 * z * (x ^ 2)⁻¹)) := by
  have h3 : x ^ 3 * z * (x ^ 3)⁻¹ = z := by
    have h := Subgroup.mem_centralizer_iff.mp (hN hx3) z hz
    rw [← h, mul_inv_cancel_right]
  have ha : x * z * x⁻¹ ∈ V := ConjAut.conj_mem V hxV hz
  have hb : x ^ 2 * z * (x ^ 2)⁻¹ ∈ V :=
    ConjAut.conj_mem V (Subgroup.pow_mem _ hxV 2) hz
  calc x * (z * ((x * z * x⁻¹) * (x ^ 2 * z * (x ^ 2)⁻¹))) * x⁻¹ =
        (x * z * x⁻¹) * (x ^ 2 * z * (x ^ 2)⁻¹) * (x ^ 3 * z * (x ^ 3)⁻¹) := by group
    _ = z * ((x * z * x⁻¹) * (x ^ 2 * z * (x ^ 2)⁻¹)) := by
      rw [h3]; exact setLike_mul_comm (V.mul_mem ha hb) hz

theorem comm_eq_one_or_eq_of_closure {V : Subgroup G} [IsMulCommutative ↥V] {t e : G}
    (ht : t ∈ Subgroup.normalizer (V : Set G)) (he : e * e = 1) {S : Set G}
    (hS : Subgroup.closure S = V)
    (hgen : ∀ s ∈ S, t * s * t⁻¹ * s⁻¹ = 1 ∨ t * s * t⁻¹ * s⁻¹ = e) :
    ∀ u ∈ V, t * u * t⁻¹ * u⁻¹ = 1 ∨ t * u * t⁻¹ * u⁻¹ = e := by
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_left he
  intro u hu
  rw [← hS] at hu
  induction hu using Subgroup.closure_induction with
  | mem s hs => exact hgen s hs
  | one => left; group
  | mul a b ha hb iha ihb =>
    have ha' : a ∈ V := hS ▸ ha
    have hb' : b ∈ V := hS ▸ hb
    have htb : t * b * t⁻¹ ∈ V := ConjAut.conj_mem V ht hb'
    have e1 : t * (a * b) * t⁻¹ * (a * b)⁻¹ =
        (t * a * t⁻¹ * a⁻¹) * (t * b * t⁻¹ * b⁻¹) := by
      have hcomm : (t * b * t⁻¹ * b⁻¹) * a⁻¹ = a⁻¹ * (t * b * t⁻¹ * b⁻¹) :=
        setLike_mul_comm (V.mul_mem htb (V.inv_mem hb')) (V.inv_mem ha')
      calc t * (a * b) * t⁻¹ * (a * b)⁻¹ =
          (t * a * t⁻¹) * ((t * b * t⁻¹ * b⁻¹) * a⁻¹) := by group
        _ = (t * a * t⁻¹ * a⁻¹) * (t * b * t⁻¹ * b⁻¹) := by rw [hcomm]; group
    rw [e1]
    rcases iha with h1 | h1 <;> rcases ihb with h2 | h2 <;> rw [h1, h2]
    · left; group
    · right; group
    · right; group
    · left; exact he
  | inv a ha iha =>
    have ha' : a ∈ V := hS ▸ ha
    have hta : t * a * t⁻¹ ∈ V := ConjAut.conj_mem V ht ha'
    have e1 : t * a⁻¹ * t⁻¹ * a⁻¹⁻¹ = (t * a * t⁻¹ * a⁻¹)⁻¹ := by
      have hcomm : (t * a * t⁻¹)⁻¹ * a = a * (t * a * t⁻¹)⁻¹ :=
        setLike_mul_comm (V.inv_mem hta) ha'
      calc t * a⁻¹ * t⁻¹ * a⁻¹⁻¹ = (t * a * t⁻¹)⁻¹ * a := by group
        _ = a * (t * a * t⁻¹)⁻¹ := hcomm
        _ = (t * a * t⁻¹ * a⁻¹)⁻¹ := by group
    rw [e1]
    rcases iha with h1 | h1 <;> rw [h1]
    · left; group
    · right; exact hei

variable {G₀ G₁ G₂ T Z : Subgroup G} [Finite G]

theorem exists_crit_flag_three (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : critB G₀ G₁ G₂ Z = 3) :
    ∃ μ δ δ' : CosetGeom G₀ G₁ G₂, vtype μ = false ∧ δ ∈ nbrs μ ∧ δ' ∈ nbrs μ ∧ δ ≠ δ' ∧
      ¬ Vv Z δ ≤ ballStab 1 δ' := by
  have hG := hc.amalgam.gen
  obtain ⟨α', hdist, hnZ⟩ := exists_dist_eq_critB hc
  rw [hb] at hdist
  obtain ⟨α₂, hα₂, hα₂d⟩ := CosetGeom.exists_adj_dist_eq hG (α := γ₀ G₀ G₁ G₂) (δ := α') (d := 2)
    (by omega)
  obtain ⟨α₁, hα₁, hα₁d⟩ := CosetGeom.exists_adj_dist_eq hG (α := γ₀ G₀ G₁ G₂) (δ := α₂) (d := 1)
    (by omega)
  have hvα₂ : vtype α₂ = false := by
    rw [vtype_eq_of_dist hc CosetGeom.vtype_γ₀ 2 α₂ hα₂d]
    decide
  have hadj : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) α₁ := CosetGeom.dist_eq_one_iff_adj.mp hα₁d
  have hvα₁ : vtype α₁ = true := vtype_eq_true_of_mem_nbrs CosetGeom.vtype_γ₀ hadj
  have hZ : Z ≤ Vv Z α₁ := by
    have h := Vv_le_Vv_of_mem_nbrs (Z := Z) hvα₁ (CosetGeom.mem_nbrs_symm hadj)
    rwa [CosetGeom.Vv_γ₀ hc.normalizes] at h
  refine ⟨α₂, α₁, α', hvα₂, hα₁, CosetGeom.mem_nbrs_symm hα₂, ?_, fun h => hnZ (hZ.trans h)⟩
  rintro rfl
  omega

theorem not_Vv_le_ballStab_of_three (hc : CritAmalgam G₀ G₁ G₂ T Z)
    (hb : critB G₀ G₁ G₂ Z = 3) {L : Subgroup G} (hL : BenderLocal (γ₀ G₀ G₁ G₂) L)
    {μ δ δ' : CosetGeom G₀ G₁ G₂} (hμ : vtype μ = false) (hδ : δ ∈ nbrs μ) (hδ' : δ' ∈ nbrs μ)
    (hne : δ ≠ δ') : ¬ Vv Z δ ≤ ballStab 1 δ' := by
  obtain ⟨μ₀, δ₀, δ₀', hμ₀, hδ₀, hδ₀', hne₀, hnot⟩ := exists_crit_flag_three hc hb
  obtain ⟨g₁, hg₁⟩ := CosetGeom.exists_smul_eq_γ₀ hμ₀
  obtain ⟨g₂, hg₂⟩ := CosetGeom.exists_smul_eq_γ₀ hμ
  have hk : (g₂ * g₁⁻¹) • μ₀ = μ := by rw [hg₁, hg₂, smul_smul, inv_mul_cancel_right]
  have hLμ : BenderLocal μ (conjSub (g₂ : G) L) := by
    rw [hg₂]
    exact hL.smul g₂
  have hkδ₀ : (g₂ * g₁⁻¹) • δ₀ ∈ nbrs μ := by
    rw [← hk]
    exact (CosetGeom.smul_adj _).mpr hδ₀
  obtain ⟨h, hhL, hh⟩ := hLμ.trans _ hkδ₀ δ hδ
  obtain ⟨g, hgμ, hgδ⟩ : ∃ g : ↥G₀, g • μ₀ = μ ∧ g • δ₀ = δ := by
    refine ⟨h * (g₂ * g₁⁻¹), ?_, ?_⟩
    · rw [mul_smul, hk]
      exact CosetGeom.smul_eq_of_mem_stab (hLμ.le_stab hhL)
    · rw [mul_smul, hh]
  have hε : g • δ₀' ∈ nbrs μ := by
    rw [← hgμ]
    exact (CosetGeom.smul_adj g).mpr hδ₀'
  have hεne : g • δ₀' ≠ δ := by
    rw [← hgδ]
    exact fun h' => hne₀ (smul_left_cancel g h').symm
  obtain ⟨U, -, -, hUδ, hUtrans, -, -⟩ := hLμ.unipotent δ hδ
  obtain ⟨u, huU, hu⟩ := hUtrans _ hε δ' hδ' hεne (Ne.symm hne)
  have huδ : u • δ = δ := CosetGeom.smul_eq_of_mem_stab (hUδ huU)
  intro hle
  apply hnot
  have h1 : Vv Z ((u * g) • δ₀) ≤ ballStab 1 ((u * g) • δ₀') := by
    rw [mul_smul, mul_smul, hgδ, huδ, hu]
    exact hle
  rwa [CosetGeom.Vv_smul hc.normalizes, CosetGeom.ballStab_smul, conjSub_le_conjSub_iff] at h1

theorem Vv_le_ballStab_of_three (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : critB G₀ G₁ G₂ Z = 3)
    {μ δ : CosetGeom G₀ G₁ G₂} (hμ : vtype μ = false) (hδ : δ ∈ nbrs μ) :
    Vv Z δ ≤ ballStab 1 μ := by
  have hδv : vtype δ = true := vtype_eq_true_of_mem_nbrs hμ hδ
  have hd : CosetGeom.dist δ μ = 1 :=
    CosetGeom.dist_eq_one_iff_adj.mpr (CosetGeom.mem_nbrs_symm hδ)
  exact (lemma72_small hc hδv (by omega)).trans (lemma63_1 hc hμ).2

theorem Vv_le_stab_inf_of_three (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : critB G₀ G₁ G₂ Z = 3)
    {μ δ δ' : CosetGeom G₀ G₁ G₂} (hμ : vtype μ = false) (hδ : δ ∈ nbrs μ)
    (hδ' : δ' ∈ nbrs μ) : Vv Z δ ≤ stab δ' ⊓ stab μ := fun u hu => by
  have h := Vv_le_ballStab_of_three hc hb hμ hδ hu
  exact ⟨CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hδ').le h,
    CosetGeom.ballStab_le_stab 1 μ h⟩

theorem mul_ne_mul_of_three (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : critB G₀ G₁ G₂ Z = 3)
    {p : ℕ} {X₀ : Subgroup G} (hbase : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀)
    {μ δ δ' : CosetGeom G₀ G₁ G₂} (hμ : vtype μ = false) (hδ : δ ∈ nbrs μ) (hδ' : δ' ∈ nbrs μ)
    {v w : G} (hv : v ∈ Vv Z δ) (hvN : v ∉ ballStab 1 δ') (hw : w ∈ Vv Z δ')
    (hwN : w ∉ ballStab 1 δ) : v * w ≠ w * v := by
  intro hvw
  have hG := hc.amalgam.gen
  have hδv : vtype δ = true := vtype_eq_true_of_mem_nbrs hμ hδ
  have hδ'v : vtype δ' = true := vtype_eq_true_of_mem_nbrs hμ hδ'
  obtain ⟨X', hX'⟩ := exists_isLocalReg_of_vtype hbase hδ'v
  have hμδ' : μ ∈ nbrs δ' := CosetGeom.mem_nbrs_symm hδ'
  have hVδ := Vv_le_stab_inf_of_three hc hb hμ hδ hδ'
  have hwδ : w ∈ stab δ := (Vv_le_stab_inf_of_three hc hb hμ hδ' hδ hw).1
  have hel := (lemma63_2' hc hδv).1
  have hvinv : v⁻¹ * w = w * v⁻¹ := by
    calc v⁻¹ * w = v⁻¹ * (w * v) * v⁻¹ := by group
      _ = v⁻¹ * (v * w) * v⁻¹ := by rw [hvw]
      _ = w * v⁻¹ := by group
  have hcomm : ∀ u ∈ Vv Z δ, u * w = w * u := by
    intro u hu
    by_cases huN : u ∈ ballStab 1 δ'
    · exact (Subgroup.mem_centralizer_iff.mp (ballStab_le_centralizer_Vv hc hδ'v huN) w hw).symm
    · have hsq : ∀ y ∈ Vv Z δ, y * y ∈ ballStab 1 δ' := fun y hy => by
        rw [← pow_two, hel.2 y hy]
        exact (ballStab 1 δ').one_mem
      have huv : u * v ∈ ballStab 1 δ' :=
        hX'.mul_mem_ker hG hμδ' (hVδ hu) (hVδ hv) (hsq u hu) (hsq v hv) huN hvN
      have h1 : (u * v) * w = w * (u * v) :=
        (Subgroup.mem_centralizer_iff.mp (ballStab_le_centralizer_Vv hc hδ'v huv) w hw).symm
      calc u * w = (u * v) * (v⁻¹ * w) := by group
        _ = (u * v) * (w * v⁻¹) := by rw [hvinv]
        _ = ((u * v) * w) * v⁻¹ := by group
        _ = (w * (u * v)) * v⁻¹ := by rw [h1]
        _ = w * u := by group
  exact hwN (mem_ballStab_of_centralizes hc hδv hwδ
    (Subgroup.mem_centralizer_iff.mpr fun u hu => hcomm u hu))

theorem comm_eq_one_or_pairProd (hc : CritAmalgam G₀ G₁ G₂ T Z) {δ : CosetGeom G₀ G₁ G₂}
    (hδ : δ ∈ nbrs (γ₀ G₀ G₁ G₂)) {X : Subgroup G} (hX : IsLocalReg δ 3 X) {x : G} (hx : x ∈ X)
    (hxN : x ∉ ballStab 1 δ) {z : G}
    (hV : Vv Z δ = Subgroup.zpowers z ⊔ Subgroup.zpowers (x * z * x⁻¹) ⊔
      Subgroup.zpowers (x ^ 2 * z * (x ^ 2)⁻¹))
    {t : G} (ht : t ∈ stab δ ⊓ stab (γ₀ G₀ G₁ G₂)) (htt : t * t ∈ ballStab 1 δ)
    (htN : t ∉ ballStab 1 δ) (htz : t * z * t⁻¹ = z) :
    ∀ u ∈ Vv Z δ, t * u * t⁻¹ * u⁻¹ = 1 ∨
      t * u * t⁻¹ * u⁻¹ = (x * z * x⁻¹) * (x ^ 2 * z * (x ^ 2)⁻¹) := by
  have hG := hc.amalgam.gen
  have hδv : vtype δ = true := vtype_eq_true_of_mem_nbrs CosetGeom.vtype_γ₀ hδ
  have h2' := lemma63_2' hc hδv
  haveI : IsMulCommutative ↥(Vv Z δ) := h2'.1.1
  have hnorm : stab δ ≤ Subgroup.normalizer (Vv Z δ : Set G) := h2'.2.2.2.2
  have hγ₀ : γ₀ G₀ G₁ G₂ ∈ nbrs δ := CosetGeom.mem_nbrs_symm hδ
  have hzV : z ∈ Vv Z δ := by
    rw [hV]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have hxV : x ∈ Subgroup.normalizer (Vv Z δ : Set G) := hnorm (hX.le_stab hx)
  have hinv := (hX.mem_ker_or_inv hG hγ₀ ht htt).resolve_left htN
  obtain ⟨hs1, hs2⟩ := conj_swap_of_inv (ballStab_le_centralizer_Vv hc hδv) hxV
    (hX.pow_mem_ker hx) hzV htz (hinv x hx)
  have haV : x * z * x⁻¹ ∈ Vv Z δ := ConjAut.conj_mem _ hxV hzV
  have hbV : x ^ 2 * z * (x ^ 2)⁻¹ ∈ Vv Z δ :=
    ConjAut.conj_mem _ (Subgroup.pow_mem _ hxV 2) hzV
  obtain ⟨a, hadef⟩ : ∃ a, x * z * x⁻¹ = a := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b, x ^ 2 * z * (x ^ 2)⁻¹ = b := ⟨_, rfl⟩
  rw [hadef] at haV
  rw [hbdef] at hbV
  rw [hadef, hbdef] at hV hs1 hs2 ⊢
  have ha2 : a * a = 1 := by rw [← pow_two]; exact h2'.1.2 a haV
  have hb2 : b * b = 1 := by rw [← pow_two]; exact h2'.1.2 b hbV
  have hab : a * b = b * a := setLike_mul_comm haV hbV
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb2
  refine comm_eq_one_or_eq_of_closure (hnorm ht.1) ?_ (S := {z, a, b}) ?_ ?_
  · calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  · rw [hV, Set.insert_eq, Set.insert_eq, Subgroup.closure_union, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure, sup_assoc]
  · rintro s (rfl | rfl | rfl)
    · left
      rw [htz]
      group
    · right
      rw [hs1, hai, hab]
    · right
      rw [hs2, hbi]

theorem pairProd_eq_of_three (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : critB G₀ G₁ G₂ Z = 3)
    {L : Subgroup G} (hL : BenderLocal (γ₀ G₀ G₁ G₂) L) {X₀ : Subgroup G}
    (hbase : IsLocalReg (γ₁ G₀ G₁ G₂) 3 X₀) {z : G}
    (hzc : ∀ g ∈ stab (γ₀ G₀ G₁ G₂), g * z = z * g) {δ δ' : CosetGeom G₀ G₁ G₂}
    (hδ : δ ∈ nbrs (γ₀ G₀ G₁ G₂)) (hδ' : δ' ∈ nbrs (γ₀ G₀ G₁ G₂)) (hne : δ ≠ δ')
    {X X' : Subgroup G} (hX : IsLocalReg δ 3 X) (hX' : IsLocalReg δ' 3 X') {x x' : G}
    (hx : x ∈ X) (hxN : x ∉ ballStab 1 δ) (hx' : x' ∈ X') (hx'N : x' ∉ ballStab 1 δ')
    (hV : Vv Z δ = Subgroup.zpowers z ⊔ Subgroup.zpowers (x * z * x⁻¹) ⊔
      Subgroup.zpowers (x ^ 2 * z * (x ^ 2)⁻¹))
    (hV' : Vv Z δ' = Subgroup.zpowers z ⊔ Subgroup.zpowers (x' * z * x'⁻¹) ⊔
      Subgroup.zpowers (x' ^ 2 * z * (x' ^ 2)⁻¹)) :
    (x * z * x⁻¹) * (x ^ 2 * z * (x ^ 2)⁻¹) = (x' * z * x'⁻¹) * (x' ^ 2 * z * (x' ^ 2)⁻¹) := by
  have hμ : vtype (γ₀ G₀ G₁ G₂) = false := CosetGeom.vtype_γ₀
  have hδ'v : vtype δ' = true := vtype_eq_true_of_mem_nbrs hμ hδ'
  obtain ⟨v, hv, hvN⟩ :=
    SetLike.not_le_iff_exists.mp (not_Vv_le_ballStab_of_three hc hb hL hμ hδ hδ' hne)
  obtain ⟨w, hw, hwN⟩ :=
    SetLike.not_le_iff_exists.mp (not_Vv_le_ballStab_of_three hc hb hL hμ hδ' hδ hne.symm)
  have hne1 := mul_ne_mul_of_three hc hb hbase hμ hδ hδ' hv hvN hw hwN
  have hvst := Vv_le_stab_inf_of_three hc hb hμ hδ hδ' hv
  have hwst := Vv_le_stab_inf_of_three hc hb hμ hδ' hδ hw
  have hsq : ∀ {ε : CosetGeom G₀ G₁ G₂}, vtype ε = true → ∀ y ∈ Vv Z ε, y * y = 1 :=
    fun hε y hy => by rw [← pow_two]; exact (lemma63_2' hc hε).1.2 y hy
  have hvv : v * v = 1 := hsq (vtype_eq_true_of_mem_nbrs hμ hδ) v hv
  have hww : w * w = 1 := hsq hδ'v w hw
  have hwz : w * z * w⁻¹ = z := by rw [hzc w hwst.2, mul_inv_cancel_right]
  have hvz : v * z * v⁻¹ = z := by rw [hzc v hvst.2, mul_inv_cancel_right]
  have h1 := comm_eq_one_or_pairProd hc hδ hX hx hxN hV ⟨hwst.1, hwst.2⟩
    (by rw [hww]; exact (ballStab 1 δ).one_mem) hwN hwz v hv
  have h2 := comm_eq_one_or_pairProd hc hδ' hX' hx' hx'N hV' ⟨hvst.1, hvst.2⟩
    (by rw [hvv]; exact (ballStab 1 δ').one_mem) hvN hvz w hw
  have hc1 : w * v * w⁻¹ * v⁻¹ ≠ 1 := fun h => hne1 (by
    have : w * v = v * w := by
      calc w * v = (w * v * w⁻¹ * v⁻¹) * v * w := by group
        _ = v * w := by rw [h, one_mul]
    exact this.symm)
  have hc2 : v * w * v⁻¹ * w⁻¹ ≠ 1 := fun h => hne1 (by
    calc v * w = (v * w * v⁻¹ * w⁻¹) * w * v := by group
      _ = w * v := by rw [h, one_mul])
  have e1 := h1.resolve_left hc1
  have e2 := h2.resolve_left hc2
  have hcV : v * w * v⁻¹ * w⁻¹ ∈ Vv Z δ' := by
    have hnorm := (lemma63_2' hc hδ'v).2.2.2.2
    exact (Vv Z δ').mul_mem (ConjAut.conj_mem _ (hnorm hvst.1) hw) ((Vv Z δ').inv_mem hw)
  have hcc := hsq hδ'v _ hcV
  have hinv : w * v * w⁻¹ * v⁻¹ = v * w * v⁻¹ * w⁻¹ := by
    have h' : w * v * w⁻¹ * v⁻¹ = (v * w * v⁻¹ * w⁻¹)⁻¹ := by group
    rw [h', inv_eq_of_mul_eq_one_left hcc]
  exact e1.symm.trans (hinv.trans e2)

theorem eq_one_of_mem_Vv_of_centralizes (hc : CritAmalgam G₀ G₁ G₂ T Z)
    {δ : CosetGeom G₀ G₁ G₂} (hδ : vtype δ = true) {y : G} (hy : y ∈ Vv Z δ)
    (hG0 : G₀ ≤ Subgroup.centralizer ({y} : Set G)) : y = 1 := by
  have hyG0 : y ∈ Subgroup.centralizer (G₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact ((Subgroup.mem_centralizer_iff.mp (hG0 hg)) y rfl).symm
  have hN : G₀ ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff.mpr ((Subgroup.zpowers_le).mpr hyG0)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hpg : IsPGroup 2 (Subgroup.zpowers y) :=
    (isPGroup_of_isElemAbelian (lemma63_2' hc hδ).1).to_le ((Subgroup.zpowers_le).mpr hy)
  have hyG : y ∈ G₀ :=
    CosetGeom.stab_le δ (pCoreOf_le 2 _ ((lemma63_2' hc hδ).2.1 hy))
  have hle : Subgroup.zpowers y ≤ pCoreOf 2 G₀ :=
    le_pCoreOf_of_le_normalizer 2 ((Subgroup.zpowers_le).mpr hyG) hN hpg
  rw [hc.amalgam.o2_trivial] at hle
  exact Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers y))

theorem card_Vv_ne_eight_of_three (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : critB G₀ G₁ G₂ Z = 3)
    {L : Subgroup G} (hL : BenderLocal (γ₀ G₀ G₁ G₂) L) {p : ℕ} {X₀ : Subgroup G}
    (hbase : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) : Nat.card (Vv Z (γ₁ G₀ G₁ G₂)) ≠ 8 := by
  intro h8
  have hG := hc.amalgam.gen
  have hodd : Odd (critB G₀ G₁ G₂ Z) := by rw [hb]; decide
  obtain ⟨hp3, hZ, hVsup⟩ := corollary77 hc hodd hbase
  subst hp3
  obtain ⟨z, hzZ, -, hzc⟩ := hZ (γ₀ G₀ G₁ G₂) CosetGeom.vtype_γ₀
  obtain ⟨x, hx, hxN⟩ := hbase.exists_not_mem
  have hγ₁ : γ₁ G₀ G₁ G₂ ∈ nbrs (γ₀ G₀ G₁ G₂) := CosetGeom.adj_γ₀_γ₁
  have hγ₀ : γ₀ G₀ G₁ G₂ ∈ nbrs (γ₁ G₀ G₁ G₂) := CosetGeom.mem_nbrs_symm hγ₁
  have hv₁ : vtype (γ₁ G₀ G₁ G₂) = true := CosetGeom.vtype_γ₁
  have hV₀ := hVsup _ hv₁ X₀ hbase _ hγ₀ x hx hxN z hzZ
  have h2' := lemma63_2' hc hv₁
  haveI : IsMulCommutative ↥(Vv Z (γ₁ G₀ G₁ G₂)) := h2'.1.1
  have hnorm := h2'.2.2.2.2
  have hcent := ballStab_le_centralizer_Vv hc hv₁
  have hxV : x ∈ Subgroup.normalizer (Vv Z (γ₁ G₀ G₁ G₂) : Set G) := hnorm (hbase.le_stab hx)
  have hzV : z ∈ Vv Z (γ₁ G₀ G₁ G₂) := by
    rw [hV₀]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have haV : x * z * x⁻¹ ∈ Vv Z (γ₁ G₀ G₁ G₂) := ConjAut.conj_mem _ hxV hzV
  have hbV : x ^ 2 * z * (x ^ 2)⁻¹ ∈ Vv Z (γ₁ G₀ G₁ G₂) :=
    ConjAut.conj_mem _ (Subgroup.pow_mem _ hxV 2) hzV
  have hxfix := conj_orbitProd_eq hcent hxV (hbase.pow_mem_ker hx) hzV
  obtain ⟨a, hadef⟩ : ∃ a, x * z * x⁻¹ = a := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b, x ^ 2 * z * (x ^ 2)⁻¹ = b := ⟨_, rfl⟩
  have hV : Vv Z (γ₁ G₀ G₁ G₂) = Subgroup.zpowers z ⊔ Subgroup.zpowers a ⊔
      Subgroup.zpowers b := by
    rw [hV₀, hadef, hbdef]
  rw [hadef] at haV
  rw [hbdef] at hbV
  rw [hadef, hbdef] at hxfix
  have hab : a * b = b * a := setLike_mul_comm haV hbV
  have hdV : z * (a * b) ∈ Vv Z (γ₁ G₀ G₁ G₂) :=
    (Vv Z _).mul_mem hzV ((Vv Z _).mul_mem haV hbV)
  have hd1 : z * (a * b) ≠ 1 := by
    intro hd1
    have hb' : b = (z * a)⁻¹ := eq_inv_of_mul_eq_one_right (by rw [mul_assoc]; exact hd1)
    have hle : Vv Z (γ₁ G₀ G₁ G₂) ≤ Subgroup.zpowers z ⊔ Subgroup.zpowers a := by
      rw [hV]
      refine sup_le le_rfl ((Subgroup.zpowers_le).mpr ?_)
      rw [hb']
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))
    have hzle : Subgroup.zpowers z ≤ Vv Z (γ₁ G₀ G₁ G₂) := (Subgroup.zpowers_le).mpr hzV
    have hale : Subgroup.zpowers a ≤ Vv Z (γ₁ G₀ G₁ G₂) := (Subgroup.zpowers_le).mpr haV
    have hc4 := card_sup_le_of_le_normalizer (le_normalizer_of_le_comm hzle hale)
    have hz2 := card_zpowers_le_two_of_sq (h2'.1.2 z hzV)
    have ha2 := card_zpowers_le_two_of_sq (h2'.1.2 a haV)
    have h3 := Subgroup.card_le_of_le hle
    have h4 := Nat.mul_le_mul hz2 ha2
    omega
  have hG₂ : stab (γ₁ G₀ G₁ G₂) ≤ Subgroup.centralizer ({z * (a * b)} : Set G) := by
    refine (hbase.le_sup_zpowers hG hγ₀ hx hxN).trans (sup_le ?_ ((Subgroup.zpowers_le).mpr ?_))
    · intro t ht
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases htN : t ∈ ballStab 1 (γ₁ G₀ G₁ G₂)
      · exact ((Subgroup.mem_centralizer_iff.mp (hcent htN)) _ hdV).symm
      · have htt : t * t ∈ ballStab 1 (γ₁ G₀ G₁ G₂) := by
          rw [← pow_two]
          exact hbase.pow_pred_mem hG hγ₀ ht
        have hinv := (hbase.mem_ker_or_inv hG hγ₀ ht htt).resolve_left htN
        have htz : t * z * t⁻¹ = z := by rw [hzc t ht.2, mul_inv_cancel_right]
        obtain ⟨hs1, hs2⟩ := conj_swap_of_inv hcent hxV (hbase.pow_mem_ker hx) hzV htz (hinv x hx)
        rw [hadef, hbdef] at hs1 hs2
        exact comm_of_conj_eq_self (conj_mul_pair_eq htz hs1 hs2 hab)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact comm_of_conj_eq_self hxfix
  have hG₁ : G₁ ≤ Subgroup.centralizer ({z * (a * b)} : Set G) := by
    intro g hg
    have hgst : g ∈ stab (γ₀ G₀ G₁ G₂) := by rw [hc.stab_γ₀_eq]; exact hg
    obtain ⟨k, rfl⟩ : ∃ k : ↥G₀, (k : G) = g := ⟨⟨g, CosetGeom.stab_le _ hgst⟩, rfl⟩
    by_cases hkγ : k • γ₁ G₀ G₁ G₂ = γ₁ G₀ G₁ G₂
    · exact hG₂ (CosetGeom.mem_stab_of_smul_eq hkγ)
    have hkγ₀ : k • γ₀ G₀ G₁ G₂ = γ₀ G₀ G₁ G₂ := CosetGeom.smul_eq_of_mem_stab hgst
    have hδ'n : k • γ₁ G₀ G₁ G₂ ∈ nbrs (γ₀ G₀ G₁ G₂) := by
      have h := (CosetGeom.smul_adj k (u := γ₀ G₀ G₁ G₂) (v := γ₁ G₀ G₁ G₂)).mpr
        CosetGeom.adj_γ₀_γ₁
      rw [hkγ₀] at h
      exact h
    have hX' : IsLocalReg (k • γ₁ G₀ G₁ G₂) 3 (conjSub (k : G) X₀) := hbase.smul k
    have hek : (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * (k : G) = x := by group
    have hx' : (k : G) * x * (k : G)⁻¹ ∈ conjSub (k : G) X₀ := by
      rw [mem_conjSub, hek]
      exact hx
    have hx'N : (k : G) * x * (k : G)⁻¹ ∉ ballStab 1 (k • γ₁ G₀ G₁ G₂) := by
      rw [CosetGeom.ballStab_smul, mem_conjSub, hek]
      exact hxN
    have hv' : vtype (k • γ₁ G₀ G₁ G₂) = true := by
      rw [CosetGeom.vtype_smul]
      exact hv₁
    have hV' := hVsup _ hv' _ hX' _ (CosetGeom.mem_nbrs_symm hδ'n) _ hx' hx'N z hzZ
    have hpair := pairProd_eq_of_three hc hb hL hbase hzc hγ₁ hδ'n (Ne.symm hkγ) hbase hX'
      hx hxN hx' hx'N hV₀ hV'
    have hkz : (k : G) * z * (k : G)⁻¹ = z := by rw [hzc _ hgst, mul_inv_cancel_right]
    have hsq : ((k : G) * x * (k : G)⁻¹) ^ 2 = (k : G) * x ^ 2 * (k : G)⁻¹ := by
      rw [pow_two, pow_two]
      group
    have ea : (k : G) * a * (k : G)⁻¹ =
        ((k : G) * x * (k : G)⁻¹) * z * ((k : G) * x * (k : G)⁻¹)⁻¹ := by
      rw [← hadef]
      calc (k : G) * (x * z * x⁻¹) * (k : G)⁻¹ =
          ((k : G) * x * (k : G)⁻¹) * ((k : G) * z * (k : G)⁻¹) *
            ((k : G) * x * (k : G)⁻¹)⁻¹ := by group
        _ = _ := by rw [hkz]
    have eb : (k : G) * b * (k : G)⁻¹ =
        ((k : G) * x * (k : G)⁻¹) ^ 2 * z * (((k : G) * x * (k : G)⁻¹) ^ 2)⁻¹ := by
      rw [← hbdef, hsq]
      calc (k : G) * (x ^ 2 * z * (x ^ 2)⁻¹) * (k : G)⁻¹ =
          ((k : G) * x ^ 2 * (k : G)⁻¹) * ((k : G) * z * (k : G)⁻¹) *
            ((k : G) * x ^ 2 * (k : G)⁻¹)⁻¹ := by group
        _ = _ := by rw [hkz]
    have e : (k : G) * (z * (a * b)) * (k : G)⁻¹ = z * (a * b) := by
      calc (k : G) * (z * (a * b)) * (k : G)⁻¹ =
          ((k : G) * z * (k : G)⁻¹) * (((k : G) * a * (k : G)⁻¹) * ((k : G) * b * (k : G)⁻¹)) := by
            group
        _ = z * (a * b) := by rw [hkz, ea, eb, ← hpair, hadef, hbdef]
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_conj_eq_self e
  have hG₂' : G₂ ≤ Subgroup.centralizer ({z * (a * b)} : Set G) := fun g hg =>
    hG₂ (by rw [hc.stab_γ₁_eq]; exact hg)
  have hG0 : G₀ ≤ Subgroup.centralizer ({z * (a * b)} : Set G) := by
    rw [hG]
    exact sup_le hG₁ hG₂'
  exact hd1 (eq_one_of_mem_Vv_of_centralizes hc hv₁ hdV hG0)

end CFSG.Quasithin.F112Crit

end
