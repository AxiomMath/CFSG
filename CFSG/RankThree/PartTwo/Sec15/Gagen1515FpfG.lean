module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfConj
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfX0
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfOmega
import CFSG.RankThree.PartTwo.Sec11.Final
import CFSG.RankThree.PartTwo.Sec13.Item134HoldsTools
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGFourSub
import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofHJ
import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.TripleCover
import CFSG.CharacterTheory.BrauerLinearThree.LocalTools
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_mem_center_of_conj_eq {H : Subgroup G} {a t : G} {k : ℕ}
    (haH : a ∈ Subgroup.normalizer (H : Set G)) (hak : a ^ 3 ^ k = 1)
    (htH : t ∈ H) (hconj : ∀ x ∈ H, a * x * a⁻¹ = t * x * t⁻¹) :
    (⟨t, htH⟩ : ↥H) ^ 3 ^ k ∈ Subgroup.center ↥H := by
  let σ : MulAut ↥H := H.normalizerMonoidHom ⟨a, haH⟩
  have hσapply : ∀ x : ↥H, ((σ x : ↥H) : G) = a * (x : G) * a⁻¹ :=
    fun x => Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨a, haH⟩ x
  have hσpow : ∀ m : ℕ, ∀ x : ↥H,
      (((σ ^ m) x : ↥H) : G) = a ^ m * (x : G) * (a ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, hσapply, ih, pow_succ']
      group
  have hσk : σ ^ 3 ^ k = 1 := by
    ext x
    rw [hσpow, hak]
    simp
  have hσ_eq : σ = MulAut.conj ⟨t, htH⟩ := by
    ext x
    rw [hσapply, MulAut.conj_apply]
    exact hconj x x.2
  rw [← CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.ker_conj_eq_center, MonoidHom.mem_ker,
    map_pow, ← hσ_eq, hσk]

theorem conj_eq_or_inv_of_map_zpowers {A : Subgroup G} {a c d : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A) (hdA : d ∈ A) (hc1 : c ≠ 1)
    (hcd1 : c * d ≠ 1)
    (ha : (Subgroup.zpowers c).map (MulAut.conj a).toMonoidHom = Subgroup.zpowers (c * d)) :
    a * c * a⁻¹ = c * d ∨ a * c * a⁻¹ = (c * d)⁻¹ := by
  classical
  have hcomm : Commute c d :=
    congrArg Subtype.val (hA.1.is_comm.comm ⟨c, hcA⟩ ⟨d, hdA⟩)
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hd3 : d ^ 3 = 1 := hA.2 d hdA
  have hcd3 : (c * d) ^ 3 = 1 := by
    rw [hcomm.mul_pow, hc3, hd3, mul_one]
  have hcdord : orderOf (c * d) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hcd3 hcd1
  have hmem : a * c * a⁻¹ ∈ Subgroup.zpowers (c * d) := by
    have h : (MulAut.conj a) c ∈ (Subgroup.zpowers c).map (MulAut.conj a).toMonoidHom :=
      ⟨c, Subgroup.mem_zpowers c, rfl⟩
    rw [ha] at h
    simpa [MulAut.conj_apply] using h
  rw [mem_zpowers_iff_mem_range_orderOf, hcdord, Finset.mem_image] at hmem
  obtain ⟨i, hi, hxi⟩ := hmem
  rw [Finset.mem_range] at hi
  interval_cases i
  · exfalso
    have hc_eq_one : c = 1 := by
      have h : a * c * a⁻¹ = 1 := by rw [← hxi]; simp
      calc c = a⁻¹ * (a * c * a⁻¹) * a := by group
        _ = a⁻¹ * 1 * a := by rw [h]
        _ = 1 := by group
    exact hc1 hc_eq_one
  · exact Or.inl (by simpa using hxi.symm)
  · right
    have hsq : (c * d) ^ 2 = (c * d)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← pow_succ', hcd3]
    rw [← hxi, hsq]

omit [Finite G] in
theorem mem_centralizer_inv_mul_of_conj_eq {H : Subgroup G} {a t : G}
    (hconj : ∀ x ∈ H, a * x * a⁻¹ = t * x * t⁻¹) :
    t⁻¹ * a ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : a * x * a⁻¹ = t * x * t⁻¹ := hconj x hx
  have h1 : t⁻¹ * (a * x) = x * t⁻¹ * a := by
    calc t⁻¹ * (a * x) = t⁻¹ * ((a * x * a⁻¹) * a) := by group
      _ = t⁻¹ * ((t * x * t⁻¹) * a) := by rw [hx']
      _ = x * t⁻¹ * a := by group
  calc x * (t⁻¹ * a) = x * t⁻¹ * a := by group
    _ = t⁻¹ * (a * x) := h1.symm
    _ = (t⁻¹ * a) * x := by group

omit [Finite G] in
theorem pow_inv_mul_eq_one {a t : G} {k : ℕ} (hat : a * t = t * a)
    (hak : a ^ 3 ^ k = 1) (ht3 : t ^ 3 ^ (k + 1) = 1) :
    (t⁻¹ * a) ^ 3 ^ (k + 1) = 1 := by
  have hcomm : Commute t⁻¹ a := (show Commute t a from hat.symm).inv_left
  have hak' : a ^ 3 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hak, one_pow]
  have ht' : (t⁻¹) ^ 3 ^ (k + 1) = 1 := by rw [inv_pow, ht3, inv_one]
  rw [hcomm.mul_pow, ht', hak', mul_one]

namespace Ctx

variable {A L : Subgroup G} {c d : G}

theorem exists_inner
    (h134 : Item134) (h48 : Sec4.Item4_8) (h : Ctx A c L d)
    {a : G} (haA : a ∈ Subgroup.normalizer (A : Set G)) (ha3 : ∃ k : ℕ, a ^ 3 ^ k = 1) :
    ∃ t ∈ x₀ L d, ∀ x ∈ x₀ L d, a * x * a⁻¹ = t * x * t⁻¹ := by
  obtain ⟨hperf, hcover, -, -, -, -⟩ := h.residual_facts
  obtain ⟨-, ⟨e⟩⟩ := hcover
  obtain ⟨k, hk⟩ := ha3
  haveI : Group.IsPerfect ↥(x₀ L d) := hperf
  have hmap := map_conj_x₀ h134 h48 h haA
  have haN : a ∈ Subgroup.normalizer (x₀ L d : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  let σ : MulAut ↥(x₀ L d) := (x₀ L d).normalizerMonoidHom ⟨a, haN⟩
  have hσapply : ∀ x : ↥(x₀ L d), ((σ x : ↥(x₀ L d)) : G) = a * (x : G) * a⁻¹ := by
    intro x
    exact Subgroup.normalizerMonoidHom_apply_apply_coe (x₀ L d) ⟨a, haN⟩ x
  have hpow : ∀ m : ℕ, ∀ x : ↥(x₀ L d),
      (((σ ^ m) x : ↥(x₀ L d)) : G) = a ^ m * (x : G) * (a ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, hσapply, ih, pow_succ']
      group
  have hσk : σ ^ 3 ^ k = 1 := by
    ext x
    rw [hpow, hk]
    simp
  obtain ⟨t, ht⟩ :=
    CFSG.RankThree.PartTwo.Sec21.Item2110Res3Proof.exists_eq_conj_of_tripleCover e
      (σ := σ) (k := k) hσk
  refine ⟨t, t.2, fun x hx => ?_⟩
  have h2 := congrArg
    (fun φ : MulAut ↥(x₀ L d) => (((φ ⟨x, hx⟩ : ↥(x₀ L d)) : G))) ht
  rw [hσapply] at h2
  simpa [MulAut.conj_apply, mul_assoc] using h2

theorem exists_three_part_of_mem_oThreeWPre (h : Ctx A c L d) {w : G}
    (hwP : w ∈ oThreeWPre A)
    (hwmap : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers (c * d)) :
    ∃ a b : G, w = a * b ∧ a ∈ Subgroup.normalizer (A : Set G) ∧
      (∃ k : ℕ, a ^ 3 ^ k = 1) ∧ (∀ x ∈ A, b * x * b⁻¹ = x) ∧
      (Subgroup.zpowers c).map (MulAut.conj a).toMonoidHom = Subgroup.zpowers (c * d) := by
  obtain ⟨a, ha_mem, b, hb_mem, hwab, ⟨k, hak⟩, hbcop⟩ :=
    CFSG.ComponentClassification.HarrisLit.T1.F3FG.exists_pow_mul_coprime Nat.prime_three w
  have haP : a ∈ oThreeWPre A := Subgroup.zpowers_le.mpr hwP ha_mem
  have hbP : b ∈ oThreeWPre A := Subgroup.zpowers_le.mpr hwP hb_mem
  have hPW : oThreeWPre A ≤ Subgroup.normalizer (A : Set G) := Subgroup.map_subtype_le _
  have haN : a ∈ Subgroup.normalizer (A : Set G) := hPW haP
  obtain ⟨hbN, hbW⟩ := CFSG.RankThree.PartTwo.Sec13.Holds134.mem_oThreeWPre_iff.mp hbP
  have hb_image_three : ∃ n : ℕ, (A.normalizerMonoidHom ⟨b, hbN⟩) ^ 3 ^ n = 1 := by
    obtain ⟨σ, hσ, hσeq⟩ := Subgroup.mem_map.mp hbW
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 3) (G := wStar A) ⟨σ, hσ⟩
    have hn' : σ ^ 3 ^ n = 1 := congrArg Subtype.val hn
    exact ⟨n, by rw [← hσeq, ← map_pow, hn', map_one]⟩
  have hb_image_one : orderOf (A.normalizerMonoidHom ⟨b, hbN⟩) = 1 := by
    obtain ⟨n, hn⟩ := hb_image_three
    have hord1 : orderOf (A.normalizerMonoidHom ⟨b, hbN⟩) ∣ 3 ^ n :=
      orderOf_dvd_of_pow_eq_one hn
    have hord2 : orderOf (A.normalizerMonoidHom ⟨b, hbN⟩) ∣ orderOf b := by
      have h := orderOf_map_dvd A.normalizerMonoidHom
        (⟨b, hbN⟩ : ↥(Subgroup.normalizer (A : Set G)))
      simpa using h
    exact (Nat.coprime_self _).mp
      (((Nat.Coprime.pow_left n hbcop).coprime_dvd_left hord1).coprime_dvd_right hord2)
  have hb_comm : ∀ x ∈ A, b * x * b⁻¹ = x := by
    intro x hx
    have hx' : A.normalizerMonoidHom ⟨b, hbN⟩ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [orderOf_eq_one_iff.mp hb_image_one]
      rfl
    simpa using congrArg Subtype.val hx'
  have hbc : b * c * b⁻¹ = c := hb_comm c h.sec13Data.mem_A
  have hmapb : (Subgroup.zpowers c).map (MulAut.conj b).toMonoidHom = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers]
    simpa [MulAut.conj_apply] using congrArg Subgroup.zpowers hbc
  have hmap_ab : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom =
      ((Subgroup.zpowers c).map (MulAut.conj b).toMonoidHom).map
        (MulAut.conj a).toMonoidHom := by
    rw [hwab, ← Sec11.map_conj_map_conj]
  have hma : (Subgroup.zpowers c).map (MulAut.conj a).toMonoidHom = Subgroup.zpowers (c * d) := by
    rw [hmap_ab, hmapb] at hwmap
    exact hwmap
  exact ⟨a, b, hwab, haN, ⟨k, hak⟩, hb_comm, hma⟩

theorem commute_and_pow_of_inner
    (h134 : Item134) (h48 : Sec4.Item4_8) (h : Ctx A c L d)
    {a t : G} {k : ℕ} (haA : a ∈ Subgroup.normalizer (A : Set G))
    (hak : a ^ 3 ^ k = 1) (htX : t ∈ x₀ L d)
    (hconj : ∀ x ∈ x₀ L d, a * x * a⁻¹ = t * x * t⁻¹) :
    a * t = t * a ∧ t ^ 3 ^ (k + 1) = 1 := by
  have hmap := map_conj_x₀ h134 h48 h haA
  have haN : a ∈ Subgroup.normalizer (x₀ L d : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  have hat : a * t = t * a := by
    have h := hconj t htX
    have h' : a * t * a⁻¹ = t := by simpa [mul_assoc] using h
    calc a * t = a * t * a⁻¹ * a := by group
      _ = t * a := by rw [h']
  have ht_center : (⟨t, htX⟩ : ↥(x₀ L d)) ^ 3 ^ k ∈ Subgroup.center ↥(x₀ L d) :=
    pow_mem_center_of_conj_eq haN hak htX hconj
  obtain ⟨-, -, -, hZcard, -, -, -⟩ := h.residual_facts
  have hcenter : (Subgroup.center ↥(x₀ L d)).map (x₀ L d).subtype = Subgroup.zpowers d :=
    h.center_x₀
  have hd_card : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [← hcenter, Subgroup.card_map_of_injective (x₀ L d).subtype_injective, hZcard]
  have hmem : t ^ 3 ^ k ∈ Subgroup.zpowers d := by
    rw [← hcenter]
    exact Subgroup.mem_map.mpr ⟨⟨t, htX⟩ ^ 3 ^ k, ht_center, rfl⟩
  have hcube : (t ^ 3 ^ k) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥(Subgroup.zpowers d))
      (x := ⟨t ^ 3 ^ k, hmem⟩)
    rw [hd_card] at h
    simpa using congrArg Subtype.val h
  refine ⟨hat, ?_⟩
  rw [pow_succ, pow_mul]
  exact hcube

theorem normalizer_and_conj_of_mem_inner
    (h : Ctx A c L d) {a t : G}
    (haA : a ∈ Subgroup.normalizer (A : Set G)) (htX : t ∈ x₀ L d)
    (hconj : ∀ x ∈ x₀ L d, a * x * a⁻¹ = t * x * t⁻¹) :
    t ∈ Subgroup.normalizer (A : Set G) ∧ t * c * t⁻¹ = c ∧ t * d * t⁻¹ = d := by
  obtain ⟨-, -, hAc⟩ := Sec14.j2_point_facts h.sec13Data h.conf.j2
  have hcA : c ∈ A := h.sec13Data.mem_A
  have hBle : A ⊓ L ≤ x₀ L d := h.inf_le_x₀
  have hXc : x₀ L d ≤ Subgroup.centralizer ({c} : Set G) := h.x₀_le_centralizer
  have hcenter : (Subgroup.center ↥(x₀ L d)).map (x₀ L d).subtype = Subgroup.zpowers d :=
    h.center_x₀
  obtain ⟨-, -, -, -, hdmem, -, -⟩ := h.residual_facts
  have hd_center : (⟨d, hdmem⟩ : ↥(x₀ L d)) ∈ Subgroup.center ↥(x₀ L d) := by
    have h : d ∈ (Subgroup.center ↥(x₀ L d)).map (x₀ L d).subtype := by
      rw [hcenter]
      exact Subgroup.mem_zpowers d
    obtain ⟨z, hz, hzval⟩ := Subgroup.mem_map.mp h
    have hz' : z = ⟨d, hdmem⟩ := Subtype.ext hzval
    rwa [hz'] at hz
  have htc : t * c * t⁻¹ = c := by
    have hcomm : t * c = c * t := Subgroup.mem_centralizer_singleton_iff.mp (hXc htX)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have htd : t * d * t⁻¹ = d := by
    have hcomm : t * d = d * t :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hd_center ⟨t, htX⟩)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hmapA : A.map (MulAut.conj t).toMonoidHom =
      (Subgroup.zpowers c).map (MulAut.conj t).toMonoidHom ⊔
        (A ⊓ L).map (MulAut.conj t).toMonoidHom := by
    conv_lhs => rw [hAc]
    rw [Subgroup.map_sup]
  have hAle : A.map (MulAut.conj t).toMonoidHom ≤ A := by
    rw [hmapA]
    refine sup_le ?_ ?_
    · rw [MonoidHom.map_zpowers]
      have hval : (MulAut.conj t).toMonoidHom c = c := by
        change (MulAut.conj t) c = c
        rw [MulAut.conj_apply, htc]
      rw [hval]
      exact Subgroup.zpowers_le.mpr hcA
    · rintro y ⟨x, hx, rfl⟩
      have hval : (MulAut.conj t).toMonoidHom x = a * x * a⁻¹ := by
        change (MulAut.conj t) x = a * x * a⁻¹
        rw [MulAut.conj_apply]
        exact (hconj x (hBle hx)).symm
      rw [hval]
      exact (Subgroup.mem_normalizer_iff.mp haA x).mp hx.1
  have htN : t ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    refine Subgroup.eq_of_le_of_card_ge hAle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  exact ⟨htN, htc, htd⟩

private theorem sq_conj_eq_self_of_conj_eq_inv {g c d : G}
    (hgcd : g * c * g⁻¹ = (c * d)⁻¹) (hgd : g * d * g⁻¹ = d) (hcd_comm : Commute c d) :
    g ^ 2 * c * (g ^ 2)⁻¹ = c := by
  have hstep : g ^ 2 * c * (g ^ 2)⁻¹ = g * (g * c * g⁻¹) * g⁻¹ := by
    rw [pow_two]
    group
  calc g ^ 2 * c * (g ^ 2)⁻¹ = g * (g * c * g⁻¹) * g⁻¹ := hstep
    _ = g * (c * d)⁻¹ * g⁻¹ := by rw [hgcd]
    _ = (g * (c * d) * g⁻¹)⁻¹ := by group
    _ = ((g * c * g⁻¹) * (g * d * g⁻¹))⁻¹ := by group
    _ = ((c * d)⁻¹ * d)⁻¹ := by rw [hgcd, hgd]
    _ = c := by
      have h1 : (c * d)⁻¹ * d = c⁻¹ := by
        rw [mul_inv_rev]
        rw [show d⁻¹ * c⁻¹ = c⁻¹ * d⁻¹ from hcd_comm.inv_inv.eq.symm]
        group
      rw [h1, inv_inv]

theorem false_of_conj_eq_inv_of_mem_centralizer
    (h : Ctx A c L d) {g : G}
    (hgX : g ∈ Subgroup.centralizer (x₀ L d : Set G))
    (hgpow : ∃ k : ℕ, g ^ 3 ^ k = 1) (hgcd : g * c * g⁻¹ = (c * d)⁻¹) : False := by
  obtain ⟨hcL, -, -⟩ := Sec14.j2_point_facts h.sec13Data h.conf.j2
  obtain ⟨-, -, -, -, hdmem, -, -⟩ := h.residual_facts
  have hcA : c ∈ A := h.sec13Data.mem_A
  have hc3 : c ^ 3 = 1 := h.sec13Data.isElemAbelian.2 c hcA
  have hcd_comm : Commute c d := h.sec13Data.commute hcA h.mem_d
  have hgd_comm : g * d = d * g :=
    (Subgroup.mem_centralizer_iff.mp hgX d hdmem).symm
  have hgd : g * d * g⁻¹ = d := by
    rw [hgd_comm, mul_assoc, mul_inv_cancel, mul_one]
  have hg2c : g ^ 2 * c * (g ^ 2)⁻¹ = c :=
    sq_conj_eq_self_of_conj_eq_inv hgcd hgd hcd_comm
  have hg_conj_c : g * c * g⁻¹ = c := by
    have hconj : ∀ m : ℕ, (g ^ 2) ^ m * c * ((g ^ 2) ^ m)⁻¹ = c := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ]
        calc (g ^ 2) ^ m * g ^ 2 * c * ((g ^ 2) ^ m * g ^ 2)⁻¹
            = (g ^ 2) ^ m * (g ^ 2 * c * (g ^ 2)⁻¹) * ((g ^ 2) ^ m)⁻¹ := by
              group
          _ = (g ^ 2) ^ m * c * ((g ^ 2) ^ m)⁻¹ := by rw [hg2c]
          _ = c := ih
    obtain ⟨m, hm⟩ := CFSG.BrauerLinearThree.exists_pow_eq_of_odd_orderOf
      (x := g) (by
        obtain ⟨n, hn⟩ := hgpow
        have hodd : Odd (3 ^ n) := Odd.pow (show Odd 3 by norm_num)
        exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hn))
    rw [← hm]
    exact hconj m
  have hcdinv : c * d = c⁻¹ := by
    have h' : (c * d)⁻¹ = c := hgcd ▸ hg_conj_c
    calc c * d = ((c * d)⁻¹)⁻¹ := (inv_inv (c * d)).symm
      _ = c⁻¹ := by rw [h']
  have hd_eq_c : d = c := by
    have h1 : d = c⁻¹ * c⁻¹ := by
      calc d = c⁻¹ * (c * d) := by group
        _ = c⁻¹ * c⁻¹ := by rw [hcdinv]
    have hc_inv : c⁻¹ * c⁻¹ = c := by
      rw [← mul_inv_rev]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_two, ← pow_succ]
      exact hc3
    rw [h1, hc_inv]
  exact hcL (hd_eq_c ▸ h.mem_L)

theorem exists_g_of_mem_oThreeWPre
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h : Ctx A c L d) {w : G} (hwP : w ∈ oThreeWPre A)
    (hwmap : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers (c * d)) :
    ∃ g ∈ Subgroup.normalizer (A : Set G), g ∈ Subgroup.centralizer (x₀ L d : Set G) ∧
      (∃ k : ℕ, g ^ 3 ^ k = 1) ∧
      (g * c * g⁻¹ = c * d ∨ g * c * g⁻¹ = (c * d)⁻¹) := by
  obtain ⟨hcL, -, -⟩ := Sec14.j2_point_facts h.sec13Data h.conf.j2
  have hcd_ne : c * d ≠ 1 := by
    intro h1
    apply hcL
    have hc_eq : c = d⁻¹ := by
      have h : c = (c * d) * d⁻¹ := by group
      rwa [h1, one_mul] at h
    rw [hc_eq]
    exact inv_mem h.mem_L
  obtain ⟨a, -, hwab, haN, ⟨k, hak⟩, -, hma⟩ :=
    exists_three_part_of_mem_oThreeWPre h hwP hwmap
  obtain ⟨t, htX, htconj⟩ := exists_inner h134 h48 h haN ⟨k, hak⟩
  obtain ⟨hat, ht3⟩ := commute_and_pow_of_inner h134 h48 h haN hak htX htconj
  obtain ⟨htN, htc, htd⟩ := normalizer_and_conj_of_mem_inner h haN htX htconj
  have hsign : a * c * a⁻¹ = c * d ∨ a * c * a⁻¹ = (c * d)⁻¹ :=
    conj_eq_or_inv_of_map_zpowers h.sec13Data.isElemAbelian h.sec13Data.mem_A h.mem_d
      h.sec13Data.ne_one hcd_ne hma
  let g : G := t⁻¹ * a
  have hgN : g ∈ Subgroup.normalizer (A : Set G) :=
    mul_mem (inv_mem htN) haN
  have hgX : g ∈ Subgroup.centralizer (x₀ L d : Set G) :=
    mem_centralizer_inv_mul_of_conj_eq htconj
  have hgpow : ∃ m : ℕ, g ^ 3 ^ m = 1 :=
    ⟨k + 1, pow_inv_mul_eq_one hat hak ht3⟩
  have htc' : t⁻¹ * c * t = c := by
    calc t⁻¹ * c * t = t⁻¹ * (t * c * t⁻¹) * t := by rw [htc]
      _ = c := by group
  have htd' : t⁻¹ * d * t = d := by
    calc t⁻¹ * d * t = t⁻¹ * (t * d * t⁻¹) * t := by rw [htd]
      _ = d := by group
  have htcd : t⁻¹ * (c * d) * t = c * d := by
    calc t⁻¹ * (c * d) * t = (t⁻¹ * c * t) * (t⁻¹ * d * t) := by group
      _ = c * d := by rw [htc', htd']
  have hgc_or : g * c * g⁻¹ = c * d ∨ g * c * g⁻¹ = (c * d)⁻¹ := by
    have hgc_eq : g * c * g⁻¹ = t⁻¹ * (a * c * a⁻¹) * t := by
      show (t⁻¹ * a) * c * (t⁻¹ * a)⁻¹ = t⁻¹ * (a * c * a⁻¹) * t
      group
    rw [hgc_eq]
    rcases hsign with hsgn | hsgn
    · left
      rw [hsgn, htcd]
    · right
      rw [hsgn]
      calc t⁻¹ * (c * d)⁻¹ * t = (t⁻¹ * (c * d) * t)⁻¹ := by group
        _ = (c * d)⁻¹ := by rw [htcd]
  exact ⟨g, hgN, hgX, hgpow, hgc_or⟩

theorem exists_g
    (h134 : Item134) (h48 : Sec4.Item4_8) (h : Ctx A c L d) :
    ∃ g ∈ Subgroup.normalizer (A : Set G), g ∈ Subgroup.centralizer (x₀ L d : Set G) ∧
      (∃ k : ℕ, g ^ 3 ^ k = 1) ∧ g * c * g⁻¹ = c * d := by
  obtain ⟨-, -, -, w, hwP, hwmap⟩ := omega_case2 h134 h48 h
  obtain ⟨g, hgN, hgX, hgpow, hgc_or⟩ := exists_g_of_mem_oThreeWPre h134 h48 h hwP hwmap
  refine ⟨g, hgN, hgX, hgpow, ?_⟩
  rcases hgc_or with hgcd | hgcd
  · exact hgcd
  · exfalso
    exact false_of_conj_eq_inv_of_mem_centralizer h hgX hgpow hgcd

theorem omega_eq_map_conj_pow
    (h134 : Item134) (h48 : Sec4.Item4_8) (h : Ctx A c L d)
    {g : G} (hgX : g ∈ Subgroup.centralizer (x₀ L d : Set G)) (hgc : g * c * g⁻¹ = c * d) :
    ∀ F ∈ omegaA A, ∃ i : ℕ, i < 3 ∧
      F = (Subgroup.zpowers c).map (MulAut.conj (g ^ i)).toMonoidHom := by
  classical
  obtain ⟨-, -, hrepr, -⟩ := omega_case2 h134 h48 h
  obtain ⟨-, -, -, hZcard, hdmem, -, -⟩ := h.residual_facts
  have hcenter : (Subgroup.center ↥(x₀ L d)).map (x₀ L d).subtype = Subgroup.zpowers d :=
    h.center_x₀
  have hd_card : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [← hcenter, Subgroup.card_map_of_injective (x₀ L d).subtype_injective, hZcard]
  have hdord : orderOf d = 3 := by
    rw [← Nat.card_zpowers]
    exact hd_card
  have hgd_comm : g * d = d * g :=
    (Subgroup.mem_centralizer_iff.mp hgX d hdmem).symm
  have hgd : g * d * g⁻¹ = d := by
    rw [hgd_comm, mul_assoc, mul_inv_cancel, mul_one]
  have hpow2 : g ^ 2 * c * (g ^ 2)⁻¹ = c * d ^ 2 := by
    have hstep : g ^ 2 * c * (g ^ 2)⁻¹ = g * (g * c * g⁻¹) * g⁻¹ := by
      rw [pow_two]
      group
    calc g ^ 2 * c * (g ^ 2)⁻¹ = g * (g * c * g⁻¹) * g⁻¹ := hstep
      _ = g * (c * d) * g⁻¹ := by rw [hgc]
      _ = (g * c * g⁻¹) * (g * d * g⁻¹) := by group
      _ = (c * d) * d := by rw [hgc, hgd]
      _ = c * d ^ 2 := by rw [pow_two]; group
  have hpow : ∀ i : ℕ, i < 3 →
      (Subgroup.zpowers c).map (MulAut.conj (g ^ i)).toMonoidHom =
        Subgroup.zpowers (c * d ^ i) := by
    intro i hi
    interval_cases i
    · simp
    · rw [pow_one, MonoidHom.map_zpowers, pow_one]
      have hval : (MulAut.conj g).toMonoidHom c = c * d := by
        change (MulAut.conj g) c = c * d
        rw [MulAut.conj_apply, hgc]
      rw [hval]
    · rw [MonoidHom.map_zpowers]
      have hval : (MulAut.conj (g ^ 2)).toMonoidHom c = c * d ^ 2 := by
        change (MulAut.conj (g ^ 2)) c = c * d ^ 2
        rw [MulAut.conj_apply]
        exact hpow2
      rw [hval]
  intro F hF
  obtain ⟨b, hb, rfl⟩ := hrepr F hF
  rw [mem_zpowers_iff_mem_range_orderOf, hdord, Finset.mem_image] at hb
  obtain ⟨i, hi, hbi⟩ := hb
  rw [Finset.mem_range] at hi
  exact ⟨i, hi, by rw [hpow i hi, ← hbi]⟩

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
