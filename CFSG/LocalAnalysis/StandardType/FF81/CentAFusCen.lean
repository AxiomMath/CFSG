module

public import CFSG.LocalAnalysis.StandardType.FF81.CentACore
public import CFSG.LocalAnalysis.StandardType.FF81.Defs

public section

namespace CFSG.StandardType.FF81.CentA

open RootFusionLin
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_sup_of_pow_eq_one {b : G} {L : Subgroup G} {z : Fin 3 → ↥L}
    (h : GGFF.SettingCore b L z) (hloc : LocalFacts b L z) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) {k : ℕ} (hk : x ^ 3 ^ k = 1) :
    x ∈ Subgroup.zpowers b ⊔ L := by
  let α : MulAut ↥L := GGFF.conjAut (h.nor x hx)
  have hαapply : ∀ y : ↥L, ((α y : ↥L) : G) = x * (y : G) * x⁻¹ := fun y =>
    GGFF.conjAut_apply (h.nor x hx) y
  have hconj : ∀ (m : ℕ) (y : ↥L), ((α ^ m) y : G) = x ^ m * (y : G) * (x ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
        intro y
        rw [pow_succ, MulAut.mul_apply, ih (α y), hαapply y, pow_succ]
        group
  have hα1 : α ^ (3 ^ k) = 1 := by
    ext y
    rw [hconj (3 ^ k) y, hk]
    simp
  obtain ⟨l, hl⟩ := h.model.inner_odd α (3 ^ k) (Odd.pow (n := k) (by norm_num)) hα1
  have hlx : ∀ y : ↥L, (l : G) * (y : G) * (l : G)⁻¹ = x * (y : G) * x⁻¹ := by
    intro y
    have h1 := hαapply y
    rw [hl] at h1
    simpa [MulAut.conj_apply] using h1
  let d : G := (l : G)⁻¹ * x
  have hdcommL : ∀ y ∈ L, Commute d y := by
    intro y hy
    have h1 := hlx ⟨y, hy⟩
    have h1y : x * y * x⁻¹ = (l : G) * y * (l : G)⁻¹ := by simpa using h1.symm
    show d * y = y * d
    calc d * y = (l : G)⁻¹ * (x * y) := by
          show (l : G)⁻¹ * x * y = (l : G)⁻¹ * (x * y)
          group
      _ = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹ * x) := by
          have e : x * y = (l : G) * y * (l : G)⁻¹ * x := by rw [← h1y]; group
          rw [e]
      _ = y * d := by
          show (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹ * x) = y * ((l : G)⁻¹ * x)
          group
  have hdCenb : d ∈ Subgroup.centralizer ({b} : Set G) :=
    (Subgroup.centralizer ({b} : Set G)).mul_mem
      ((Subgroup.centralizer ({b} : Set G)).inv_mem (h.le l.2)) hx
  have hld : Commute (l : G) d := (hdcommL (l : G) l.2).symm
  have hxd : x = (l : G) * d := by
    show x = (l : G) * ((l : G)⁻¹ * x)
    group
  have hprod : (l : G) ^ (3 ^ k) * d ^ (3 ^ k) = 1 := by
    rw [← hld.mul_pow, ← hxd]
    exact hk
  have hdL : d ^ (3 ^ k) ∈ L := by
    have e : d ^ (3 ^ k) = ((l : G) ^ (3 ^ k))⁻¹ := eq_inv_of_mul_eq_one_right hprod
    rw [e]
    exact L.inv_mem (L.pow_mem l.2 _)
  have hdcent : ∀ y ∈ L, d ^ (3 ^ k) * y = y * d ^ (3 ^ k) := by
    intro y hy
    exact ((hdcommL y hy).pow_left (3 ^ k)).eq
  have hdz1 : d ^ (3 ^ k) = 1 := h.eq_one_of_mem hdL hdcent
  have hPd : IsPGroup 3 (Subgroup.zpowers d) := by
    have hdvd : orderOf d ∣ 3 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hdz1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd
    refine IsPGroup.of_card (n := j) ?_
    rw [Nat.card_zpowers, hj]
  have hPb : IsPGroup 3 (Subgroup.zpowers b) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, h.ord]
    norm_num
  have hnorm : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    refine (Subgroup.zpowers_le.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hdb : Commute d b := Subgroup.mem_centralizer_singleton_iff.mp hdCenb
    exact (hdb.zpow_right j).eq.symm
  have hP3 : IsPGroup 3 (Subgroup.zpowers d ⊔ Subgroup.zpowers b : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hPd hPb hnorm
  have hPL : Subgroup.zpowers d ⊔ Subgroup.zpowers b ≤
      Subgroup.centralizer (L : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hdcommL y hy).eq.symm
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => h.comm_of_mem hy
  have hPbC : Subgroup.zpowers d ⊔ Subgroup.zpowers b ≤
      Subgroup.centralizer ({b} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr hdCenb) (Subgroup.zpowers_le.mpr ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hbP : Subgroup.zpowers b ≤ Subgroup.zpowers d ⊔ Subgroup.zpowers b := le_sup_right
  have heq := hloc.syl _ hPL hPbC hP3 hbP
  have hdP : d ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers b :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  have hdZ : d ∈ Subgroup.zpowers b := by rw [heq] at hdP; exact hdP
  have hxsup : x ∈ Subgroup.zpowers b ⊔ L := by
    have hmem := Subgroup.mul_mem_sup l.2 hdZ
    rw [hxd]
    rw [sup_comm] at hmem
    exact hmem
  exact hxsup

theorem exists_leviOne_inv_mul_mem_uSub {m : ℕ} {g : GL (BlkIdx 1 m) (ZMod 2)}
    (hg : g ∈ Cent 1 m) : ∃ R : GL (Fin m) (ZMod 2), (leviOne m R)⁻¹ * g ∈ uSub 1 m := by
  obtain ⟨a, b, c, P, R, hg'⟩ := (mem_cent_iff 1 m).mp hg
  have hP : P = 1 := glOne_eq_one P
  have hg'' : g = uGL a b c * leviOne m R := by
    rw [hg', hP]
    rfl
  refine ⟨R, ?_⟩
  rw [hg'']
  have hmem : (leviOne m R)⁻¹ ∈ Cent 1 m :=
    (Cent 1 m).inv_mem (leviB_le_cent m ⟨R, rfl⟩)
  have hconj := normal_uSub 1 m (leviOne m R)⁻¹ hmem (uGL a b c) ⟨a, b, c, rfl⟩
  simpa [mul_assoc] using hconj

private theorem cafCen_leviOne_entry {m : ℕ} (R : GL (Fin m) (ZMod 2)) (i j : Fin m) :
    ((leviOne m R : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) (Sum.inr (Sum.inl i))
        (Sum.inr (Sum.inl j)) = (R : Matrix (Fin m) (Fin m) (ZMod 2)) i j := by
  simp [leviOne, coe_levi, blk]

theorem eq_of_leviOne_inv_mul_mem_uSub {m : ℕ} {R R' : GL (Fin m) (ZMod 2)}
    (h : (leviOne m R)⁻¹ * leviOne m R' ∈ uSub 1 m) : R = R' := by
  obtain ⟨a, b, c, habc⟩ := h
  have h1 : leviOne m (R⁻¹ * R') = uGL a b c := by
    rw [map_mul, map_inv, habc]
  have h2 : ((leviOne m (R⁻¹ * R') : GL (BlkIdx 1 m) (ZMod 2)) :
      Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      ((uGL a b c : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) :=
    congrArg Units.val h1
  have hS : R⁻¹ * R' = 1 := by
    refine Units.ext ?_
    ext i j
    have h3 := congrFun₂ h2 (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j))
    rw [cafCen_leviOne_entry (R⁻¹ * R') i j] at h3
    have hu : ((uGL a b c : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) (Sum.inr (Sum.inl i))
        (Sum.inr (Sum.inl j)) = (1 : Matrix (Fin m) (Fin m) (ZMod 2)) i j := by
      simp [coe_uGL, uMat, blk]
    rw [hu] at h3
    simpa using h3
  have h2' : R * (R⁻¹ * R') = R' := by group
  simpa [hS] using h2'

theorem mem_tor_of_mem_centralizer {m : ℕ} {Y L R : Subgroup G} {b t : G}
    {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)} (hS : CentASetting m Y L R b t φ) {z : Fin 3 → ↥L}
    (hcen : ∀ k : ↥L, (∀ i, k * z i = z i * k) → ∃ v, k = vecElt z v) {y : G} (hyY : y ∈ Y)
    (hyt : y * t = t * y) (hyz : ∀ i, y * GGFF.zs z i = GGFF.zs z i * y) {k : ℕ}
    (hk : y ^ 3 ^ k = 1) : y ∈ GGFF.tor (GGFF.zs z) := by
  let yY : ↥Y := ⟨y, hyY⟩
  have hcommj : φ yY * jGL 1 m = jGL 1 m * φ yY := by
    have h1 : yY * ⟨t, hS.t_mem⟩ = ⟨t, hS.t_mem⟩ * yY := Subtype.ext hyt
    have h2 := congrArg φ h1
    simpa only [yY, map_mul, hS.φ_t] using h2
  have hgy : φ yY ∈ Cent 1 m := by
    change φ yY ∈ Subgroup.centralizer
      ({jGL 1 m} : Set (GL (BlkIdx 1 m) (ZMod 2)))
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcommj
  obtain ⟨S, hSu⟩ := exists_leviOne_inv_mul_mem_uSub hgy
  let A : GL (BlkIdx 1 m) (ZMod 2) := leviOne m S
  let u : GL (BlkIdx 1 m) (ZMod 2) := A⁻¹ * φ yY
  have hu : u ∈ uSub 1 m := hSu
  have hAu : A * u = φ yY := by
    show leviOne m S * ((leviOne m S)⁻¹ * φ yY) = φ yY
    group
  let l : ↥Y := φ.symm A
  have hlL : (l : G) ∈ L := by
    refine (hS.φ_L l).mpr ?_
    rw [show φ l = A from MulEquiv.apply_symm_apply φ A]
    exact ⟨S, rfl⟩
  have hT : ∀ i : Fin 3, ∃ T : GL (Fin m) (ZMod 2),
      leviOne m T = φ ⟨GGFF.zs z i, hS.L_le (z i).2⟩ := by
    intro i
    exact MonoidHom.mem_range.mp ((hS.φ_L ⟨GGFF.zs z i, hS.L_le (z i).2⟩).mp (z i).2)
  choose T hT' using hT
  have hcommB : ∀ i, φ yY * leviOne m (T i) = leviOne m (T i) * φ yY := by
    intro i
    have h1 : yY * ⟨GGFF.zs z i, hS.L_le (z i).2⟩ =
        ⟨GGFF.zs z i, hS.L_le (z i).2⟩ * yY := Subtype.ext (hyz i)
    have h2 := congrArg φ h1
    rw [hT' i]
    simpa only [map_mul] using h2
  have hTS : ∀ i, T i * S = S * T i := by
    intro i
    let B : GL (BlkIdx 1 m) (ZMod 2) := leviOne m (T i)
    have hBc : B ∈ Cent 1 m := leviB_le_cent m ⟨T i, rfl⟩
    have hcomm : φ yY * B = B * φ yY := hcommB i
    have hcomm' : A * u * B = B * A * u := by
      calc A * u * B = φ yY * B := by rw [hAu]
        _ = B * φ yY := hcomm
        _ = B * (A * u) := by rw [hAu]
        _ = B * A * u := by group
    have hu' : B⁻¹ * u * B ∈ uSub 1 m :=
      normal_uSub 1 m B⁻¹ ((Cent 1 m).inv_mem hBc) u hu
    have hkey : A * B * (B⁻¹ * u * B) = B * A * u := by
      calc A * B * (B⁻¹ * u * B) = A * u * B := by group
        _ = B * A * u := hcomm'
    have hcommut : (B * A)⁻¹ * (A * B) = u * (B⁻¹ * u * B)⁻¹ := by
      have h1 : ((B * A)⁻¹ * (A * B)) * (B⁻¹ * u * B) = u := by
        calc ((B * A)⁻¹ * (A * B)) * (B⁻¹ * u * B) =
            (B * A)⁻¹ * (A * B * (B⁻¹ * u * B)) := by group
          _ = (B * A)⁻¹ * (B * A * u) := by rw [hkey]
          _ = u := by group
      calc (B * A)⁻¹ * (A * B) =
          ((B * A)⁻¹ * (A * B)) * (B⁻¹ * u * B) * (B⁻¹ * u * B)⁻¹ := by group
        _ = u * (B⁻¹ * u * B)⁻¹ := by rw [h1]
    have hmem : (leviOne m (T i * S))⁻¹ * leviOne m (S * T i) ∈ uSub 1 m := by
      have hEq : (leviOne m (T i * S))⁻¹ * leviOne m (S * T i) =
          (B * A)⁻¹ * (A * B) := by
        simp only [B, A, map_mul]
      rw [hEq, hcommut]
      exact (uSub 1 m).mul_mem hu ((uSub 1 m).inv_mem hu')
    exact eq_of_leviOne_inv_mul_mem_uSub hmem
  have hAB : ∀ i, A * leviOne m (T i) = leviOne m (T i) * A := by
    intro i
    show leviOne m S * leviOne m (T i) = leviOne m (T i) * leviOne m S
    rw [← map_mul, ← map_mul, hTS i]
  have hcommL : ∀ i, (l : G) * GGFF.zs z i = GGFF.zs z i * (l : G) := by
    intro i
    have hYeq : l * ⟨GGFF.zs z i, hS.L_le (z i).2⟩ =
        ⟨GGFF.zs z i, hS.L_le (z i).2⟩ * l := by
      apply φ.injective
      rw [map_mul, map_mul]
      rw [show φ l = A from MulEquiv.apply_symm_apply φ A]
      rw [← hT' i]
      exact hAB i
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val hYeq
  obtain ⟨v, hv⟩ := hcen ⟨(l : G), hlL⟩ (by
    intro i
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using hcommL i)
  have hlval : (l : G) = vecElt (GGFF.zs z) v := by
    rw [GGFF.SettingCore.vecElt_zs z v]
    exact congrArg Subtype.val hv
  have hlmem : (l : G) ∈ GGFF.tor (GGFF.zs z) := by
    rw [hlval]
    exact GGFF.vecElt_mem_tor _ v
  have hgen : ∀ x ∈ GGFF.tor (GGFF.zs z), y * x = x * y := by
    have hsub : GGFF.tor (GGFF.zs z) ≤ Subgroup.centralizer ({y} : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, rfl⟩
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hyz i
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp (hsub hx) y (Set.mem_singleton y)
  have hyl : y * (l : G) = (l : G) * y := hgen (l : G) hlmem
  let e : G := (l : G)⁻¹ * y
  have hyle : y = (l : G) * e := by
    show y = (l : G) * ((l : G)⁻¹ * y)
    group
  have hele : Commute (l : G) e := by
    show (l : G) * ((l : G)⁻¹ * y) = ((l : G)⁻¹ * y) * (l : G)
    calc (l : G) * ((l : G)⁻¹ * y) = y := by group
      _ = ((l : G)⁻¹ * y) * (l : G) := by rw [mul_assoc, hyl]; group
  have heφ : e = ((φ.symm u : ↥Y) : G) := by
    have hsym : φ.symm u = (l : ↥Y)⁻¹ * yY := by
      show φ.symm (A⁻¹ * φ yY) = (φ.symm A)⁻¹ * yY
      rw [map_mul, map_inv, MulEquiv.symm_apply_apply]
    show (l : G)⁻¹ * y = ((φ.symm u : ↥Y) : G)
    rw [hsym]
    rfl
  let N : ℕ := 1 * 1 + 2 * 1 * m
  have hcard : Nat.card (uSub 1 m) = 2 ^ N := by
    rw [card_uSub]
  have huN : u ^ (2 ^ N) = 1 := by
    have h1 : (⟨u, hu⟩ : ↥(uSub 1 m)) ^ Nat.card (uSub 1 m) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard _)
    have h2 : u ^ Nat.card (uSub 1 m) = 1 := by
      have h2' := congrArg (fun x : ↥(uSub 1 m) => (x : GL (BlkIdx 1 m) (ZMod 2))) h1
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2'
    rwa [hcard] at h2
  have he_pow : e ^ (2 ^ N) = 1 := by
    have hYpow : (φ.symm u : ↥Y) ^ (2 ^ N) = 1 := by
      apply φ.injective
      rw [map_pow, map_one, MulEquiv.apply_symm_apply]
      exact huN
    rw [heφ, ← Subgroup.coe_pow, hYpow, Subgroup.coe_one]
  have hy2 : y ^ (2 ^ N) ∈ GGFF.tor (GGFF.zs z) := by
    rw [hyle, hele.mul_pow (2 ^ N), he_pow, mul_one]
    exact (GGFF.tor (GGFF.zs z)).pow_mem hlmem (2 ^ N)
  have hgcd : Nat.gcd (2 ^ N) (3 ^ k) = 1 :=
    Nat.Coprime.pow N k (by norm_num : Nat.Coprime 2 3)
  have hbez : ((2 ^ N : ℕ) : ℤ) * Nat.gcdA (2 ^ N) (3 ^ k) +
      ((3 ^ k : ℕ) : ℤ) * Nat.gcdB (2 ^ N) (3 ^ k) = 1 := by
    have h := Nat.gcd_eq_gcd_ab (2 ^ N) (3 ^ k)
    rw [hgcd] at h
    simpa using h.symm
  have h1 : y ^ (((2 ^ N : ℕ) : ℤ) * Nat.gcdA (2 ^ N) (3 ^ k) +
      ((3 ^ k : ℕ) : ℤ) * Nat.gcdB (2 ^ N) (3 ^ k)) = y := by
    rw [hbez, zpow_one]
  have hpow : y ^ (((2 ^ N : ℕ) : ℤ) * Nat.gcdA (2 ^ N) (3 ^ k) +
      ((3 ^ k : ℕ) : ℤ) * Nat.gcdB (2 ^ N) (3 ^ k)) =
      (y ^ (2 ^ N)) ^ Nat.gcdA (2 ^ N) (3 ^ k) := by
    rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hk, one_zpow, mul_one]
  have hy_eq : y = (y ^ (2 ^ N)) ^ Nat.gcdA (2 ^ N) (3 ^ k) := h1.symm.trans hpow
  have hmem : (y ^ (2 ^ N)) ^ Nat.gcdA (2 ^ N) (3 ^ k) ∈ GGFF.tor (GGFF.zs z) :=
    (GGFF.tor (GGFF.zs z)).zpow_mem hy2 _
  rwa [← hy_eq] at hmem

end CFSG.StandardType.FF81.CentA

end
