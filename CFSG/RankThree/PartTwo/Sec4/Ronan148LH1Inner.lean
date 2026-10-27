module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1Cent
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LNA
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A11

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)

theorem mem_normalizer_zpowers_of_conj {G : Type} [Group G] {g e : G}
    (h1 : g * e * g⁻¹ ∈ Subgroup.zpowers e) (h2 : g⁻¹ * e * g⁻¹⁻¹ ∈ Subgroup.zpowers e) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h1 k
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    have : h = (g⁻¹ * e * g⁻¹⁻¹) ^ k := by
      rw [conj_zpow, hk]
      group
    rw [this]
    exact Subgroup.zpow_mem _ h2 k

section Core

variable {G : Type} [Group G] [Finite G]

theorem false_of_inner_cent {A L : Subgroup G} (hA : Late.IsE27 A)
    (hEF : partTwoE G = partTwoF G) (hZ : Subgroup.center L = ⊥) (hcube : CubeInner L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) {d : G} (hdA : d ∈ A)
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hLd : ¬ L ≤ Subgroup.centralizer {d})
    (hCA : A ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)
    (hinv : ∀ e ∈ L, e ≠ 1 → e ^ 3 = 1 → (∀ y ∈ L, d * y * d⁻¹ = e * y * e⁻¹) →
      ∀ B : Subgroup G, B ≤ L → CFSG.Assembly.IsElemAbelian 3 B → e ∈ B →
        ∃ t ∈ L, t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ b ∈ B, t * b = b * t)
    (hext : ∀ e ∈ L, e ≠ 1 → e ^ 3 = 1 → (∀ y ∈ L, d * y * d⁻¹ = e * y * e⁻¹) →
      ∃ s ∈ L, s * e = e * s ∧ s ^ 3 = 1 ∧ s ∉ Subgroup.zpowers e)
    (hmove : ∀ e ∈ L, e ≠ 1 → e ^ 3 = 1 → (∀ y ∈ L, d * y * d⁻¹ = e * y * e⁻¹) →
      ∀ E : Subgroup G, E ≤ L → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 → e ∈ E →
        (∀ F : Subgroup G, F ≤ L → CFSG.Assembly.IsElemAbelian 3 F → E ≤ F → F = E) →
        ∃ n ∈ L, n ∈ Subgroup.normalizer (E : Set G) ∧
          n ∉ Subgroup.normalizer (Subgroup.zpowers e : Set G)) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAel : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  have hA27 : Nat.card A = 27 := hA.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := fun a ha => hAel.2 a ha
  have hAc' : ∀ a b : A, a * b = b * a := fun a b => Subtype.ext (hAc a a.2 b b.2)
  have hpow3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hA3 a a.2)
  set C := Subgroup.centralizer (L : Set G) with hCdef
  have hLC : ∀ x : G, x ∈ L → x ∈ C → x = 1 := by
    intro x hxL hxC
    have hmem : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) g g.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  obtain ⟨act, hact⟩ : ∃ act : A →* MulAut L,
      ∀ (a : A) (x : L), ((act a x : L) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    ⟨L.normalizerMonoidHom.comp (Subgroup.inclusion hAN), fun _ _ => rfl⟩
  have hact3 : ∀ a : A, act a ^ 3 = 1 := fun a => by
    rw [← map_pow, hpow3 a, map_one]
  have hcinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    refine Subtype.ext (hLC x x.2 ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h := congrArg (fun τ : MulAut L => τ ⟨g, hg⟩) hx
    have h' : (x : G) * g * (x : G)⁻¹ = g := congrArg Subtype.val h
    exact (mul_inv_eq_iff_eq_mul.mp h').symm
  have hrange : ∀ a : A, act a ∈ (MulAut.conj : L →* MulAut L).range :=
    fun a => hcube (act a) (hact3 a)
  obtain ⟨phi, hphi⟩ : ∃ phi : A →* L, ∀ a : A, MulAut.conj (phi a) = act a :=
    ⟨(MonoidHom.ofInjective hcinj).symm.toMonoidHom.comp (act.codRestrict _ hrange),
      fun a => MonoidHom.apply_ofInjective_symm hcinj ⟨act a, hrange a⟩⟩
  have hkey : ∀ (a : A) (x : L), (a : G) * (x : G) * (a : G)⁻¹ =
      ((phi a : L) : G) * (x : G) * ((phi a : L) : G)⁻¹ := by
    intro a x
    rw [← hact a x, ← hphi a]
    exact congrArg Subtype.val (MulAut.conj_apply (phi a) x)
  set rho : A →* G := L.subtype.comp phi with hrho
  have hrho_apply : ∀ a : A, rho a = ((phi a : L) : G) := fun _ => rfl
  have hrhoL : ∀ a : A, rho a ∈ L := fun a => (phi a).2
  have hrho3 : ∀ a : A, rho a ^ 3 = 1 := fun a => by rw [← map_pow, hpow3 a, map_one]
  have hzC : ∀ a : A, (rho a)⁻¹ * a ∈ C := by
    intro a
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : (a : G) * l * (a : G)⁻¹ = rho a * l * (rho a)⁻¹ := by
      rw [hrho_apply]
      exact hkey a ⟨l, hl⟩
    calc l * ((rho a)⁻¹ * a) = (rho a)⁻¹ * (rho a * l * (rho a)⁻¹) * a := by group
      _ = (rho a)⁻¹ * ((a : G) * l * (a : G)⁻¹) * a := by rw [h1]
      _ = (rho a)⁻¹ * a * l := by group
  have hPA : ∀ a b : A, rho a * b = b * rho a := by
    intro a b
    have hk : (b : G) * ((phi a : L) : G) * (b : G)⁻¹ =
        ((phi b : L) : G) * ((phi a : L) : G) * ((phi b : L) : G)⁻¹ := hkey b (phi a)
    have hc : ((phi b : L) : G) * ((phi a : L) : G) =
        ((phi a : L) : G) * ((phi b : L) : G) := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hAc' b a]
    have h2 : (b : G) * ((phi a : L) : G) * (b : G)⁻¹ = ((phi a : L) : G) := by
      rw [hk, hc, mul_inv_cancel_right]
    rw [hrho_apply]
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hPel : CFSG.Assembly.IsElemAbelian 3 rho.range := by
    refine ⟨⟨⟨fun p q => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp p.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp q.2
      change (p : G) * q = q * p
      rw [← ha, ← hb, ← map_mul, ← map_mul, hAc' a b]
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
      exact hrho3 a
  have hPL : rho.range ≤ L := by
    intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    exact hrhoL a
  set d' : A := ⟨d, hdA⟩ with hd'
  set e := rho d' with he
  have heL : e ∈ L := hrhoL d'
  have he3 : e ^ 3 = 1 := hrho3 d'
  have hde : ∀ y ∈ L, d * y * d⁻¹ = e * y * e⁻¹ := fun y hy => hkey d' ⟨y, hy⟩
  have hdC : e⁻¹ * d ∈ C := hzC d'
  have he1 : e ≠ 1 := by
    intro h1
    apply hLd
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 := Subgroup.mem_centralizer_iff.mp hdC y hy
    rw [h1, inv_one, one_mul] at h2
    exact h2
  obtain ⟨t, htL, ht1, ht2, htP⟩ :=
    hinv e heL he1 he3 hde rho.range hPL hPel (MonoidHom.mem_range.mpr ⟨d', rfl⟩)
  have htA : ∀ a ∈ A, t * a = a * t := by
    intro a ha
    have h1 : t * rho ⟨a, ha⟩ = rho ⟨a, ha⟩ * t := htP _ (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩)
    have h2 : t * ((rho ⟨a, ha⟩)⁻¹ * a) = ((rho ⟨a, ha⟩)⁻¹ * a) * t :=
      Subgroup.mem_centralizer_iff.mp (hzC ⟨a, ha⟩) t htL
    calc t * a = t * rho ⟨a, ha⟩ * ((rho ⟨a, ha⟩)⁻¹ * a) := by group
      _ = rho ⟨a, ha⟩ * (t * ((rho ⟨a, ha⟩)⁻¹ * a)) := by rw [h1, mul_assoc]
      _ = rho ⟨a, ha⟩ * (((rho ⟨a, ha⟩)⁻¹ * a) * t) := by rw [h2]
      _ = a * t := by group
  have hAt : A ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hx)
    exact ((Commute.zpow_left (show Commute t a from htA a ha) k)).eq
  have ht2' : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hAE : A ∈ partTwoE G :=
    ⟨hAel, hA27, Subgroup.zpowers t, fun h => ht1 (Subgroup.zpowers_eq_bot.mp h),
      IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, ht2'] <;> norm_num⟩, hAt⟩
  have hAF : A ∈ partTwoF G := by
    rw [← hEF]
    exact hAE
  have hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A := hAF.2.1
  have hPAsup : CFSG.Assembly.IsElemAbelian 3 (rho.range ⊔ A) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hPel hAel (fun p hp b hb => by
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hp
      exact hPA a ⟨b, hb⟩)
  have hPle : rho.range ≤ A :=
    calc rho.range ≤ rho.range ⊔ A := le_sup_left
      _ = A := hAmax _ hPAsup le_sup_right
  set E := A ⊓ L with hEdef
  set B := A ⊓ C with hBdef
  have hrhoE : ∀ a : A, rho a ∈ E := fun a =>
    ⟨hPle (MonoidHom.mem_range.mpr ⟨a, rfl⟩), hrhoL a⟩
  have hzB : ∀ a : A, (rho a)⁻¹ * a ∈ B := fun a =>
    ⟨A.mul_mem (A.inv_mem (hPle (MonoidHom.mem_range.mpr ⟨a, rfl⟩))) a.2, hzC a⟩
  have hEB : ∀ x ∈ E, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx.2
  have hEBinf : E ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxB⟩
    exact Subgroup.mem_bot.mpr (hLC x hxE.2 hxB.2)
  have hEBsup : E ⊔ B = A := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
    intro a ha
    have hmem := Subgroup.mul_mem _ (Subgroup.mem_sup_left (hrhoE ⟨a, ha⟩) :
      rho ⟨a, ha⟩ ∈ E ⊔ B) (Subgroup.mem_sup_right (hzB ⟨a, ha⟩))
    rwa [mul_inv_cancel_left] at hmem
  have hcard : Nat.card E * Nat.card B = 27 := by
    rw [← Ronan148R.card_sup_of_commute_of_inf hEB hEBinf, hEBsup, hA27]
  have heE : e ∈ E := hrhoE d'
  have hE1 : Nat.card E ≠ 1 := by
    intro h
    have h1 := Subgroup.card_eq_one.mp h
    rw [h1] at heE
    exact he1 (Subgroup.mem_bot.mp heE)
  have hB1 : Nat.card B ≠ 1 := fun h => hCA (Subgroup.card_eq_one.mp h)
  have hcases : Nat.card E = 3 ∨ Nat.card E = 9 := by
    have hEd : Nat.card E ∣ 3 ^ 3 := ⟨Nat.card B, by rw [hcard]; norm_num⟩
    have hBd : Nat.card B ∣ 3 ^ 3 := ⟨Nat.card E, by rw [mul_comm, hcard]; norm_num⟩
    obtain ⟨i, hi, hEi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hEd
    obtain ⟨j, hj, hBj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hBd
    rw [hEi, hBj] at hcard
    rw [hEi] at hE1 ⊢
    rw [hBj] at hB1
    revert hcard hE1 hB1
    interval_cases i <;> interval_cases j <;> norm_num
  rcases hcases with hE3 | hE9
  ·
    obtain ⟨s, hsL, hse, hs3, hsne⟩ := hext e heL he1 he3 hde
    have hEz : E = Subgroup.zpowers e := by
      symm
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr heE) ?_
      rw [hE3, Nat.card_zpowers, orderOf_eq_prime he3 he1]
    have hsA : ∀ a ∈ A, s * a = a * s := by
      intro a ha
      have hr : rho ⟨a, ha⟩ ∈ Subgroup.zpowers e := by
        rw [← hEz]
        exact hrhoE ⟨a, ha⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hr
      have h1 : s * rho ⟨a, ha⟩ = rho ⟨a, ha⟩ * s := by
        rw [← hk]
        exact ((Commute.zpow_right (show Commute s e from hse) k)).eq
      have h2 : s * ((rho ⟨a, ha⟩)⁻¹ * a) = ((rho ⟨a, ha⟩)⁻¹ * a) * s :=
        Subgroup.mem_centralizer_iff.mp (hzC ⟨a, ha⟩) s hsL
      calc s * a = s * rho ⟨a, ha⟩ * ((rho ⟨a, ha⟩)⁻¹ * a) := by group
        _ = rho ⟨a, ha⟩ * (s * ((rho ⟨a, ha⟩)⁻¹ * a)) := by rw [h1, mul_assoc]
        _ = rho ⟨a, ha⟩ * (((rho ⟨a, ha⟩)⁻¹ * a) * s) := by rw [h2]
        _ = a * s := by group
    have hAs : CFSG.Assembly.IsElemAbelian 3 (A ⊔ Subgroup.zpowers s) :=
      CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hAel
        (CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hs3) (fun a ha y hy => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          exact ((Commute.zpow_left (show Commute s a from hsA a ha) k)).eq.symm)
    have hsA' : s ∈ A := by
      have h1 := hAmax _ hAs le_sup_left
      rw [← h1]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
    apply hsne
    rw [← hEz]
    exact ⟨hsA', hsL⟩
  ·
    have hEL : E ≤ L := inf_le_right
    have hEel : CFSG.Assembly.IsElemAbelian 3 E := isElemAbelian_mono inf_le_left hAel
    have hBel : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_mono inf_le_left hAel
    have hEmax : ∀ F : Subgroup G, F ≤ L → CFSG.Assembly.IsElemAbelian 3 F → E ≤ F → F = E := by
      intro F hFL hF hEF'
      have hFB : CFSG.Assembly.IsElemAbelian 3 (F ⊔ B) :=
        CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hF hBel (fun x hx y hy =>
          Subgroup.mem_centralizer_iff.mp hy.2 x (hFL hx))
      have hAFB : A ≤ F ⊔ B := by
        rw [← hEBsup]
        exact sup_le_sup_right hEF' B
      have h1 := hAmax _ hFB hAFB
      refine le_antisymm (fun x hx => ⟨?_, hFL hx⟩) hEF'
      rw [← h1]
      exact Subgroup.mem_sup_left hx
    obtain ⟨n, hnL, hnE, hne⟩ := hmove e heL he1 he3 hde E hEL hEel hE9 heE hEmax
    have hnA : n ∈ Subgroup.normalizer (A : Set G) := by
      rw [← hEBsup]
      exact mem_normalizer_sup hnE (mem_normalizer_of_le_centralizer inf_le_right hnL)
    have hnd := hN hnA
    have hconj : ∀ g ∈ L, g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        g * e * g⁻¹ ∈ Subgroup.zpowers e := by
      intro g hgL hgN
      have hgd : g * d * g⁻¹ ∈ Subgroup.zpowers d :=
        (Subgroup.mem_normalizer_iff.mp hgN d).mp (Subgroup.mem_zpowers d)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgd
      set z := e⁻¹ * d with hz
      have hdez : d = e * z := by rw [hz, mul_inv_cancel_left]
      have hez : Commute e z := Subgroup.mem_centralizer_iff.mp hdC e heL
      have hgz : g * z * g⁻¹ = z := by
        rw [Subgroup.mem_centralizer_iff.mp hdC g hgL, mul_inv_cancel_right]
      have h1 : g * d * g⁻¹ = (g * e * g⁻¹) * z := by
        rw [hdez]
        calc g * (e * z) * g⁻¹ = (g * e * g⁻¹) * (g * z * g⁻¹) := by group
          _ = (g * e * g⁻¹) * z := by rw [hgz]
      have h2 : d ^ k = e ^ k * z ^ k := by
        rw [hdez]
        exact hez.mul_zpow k
      have h3 : (e ^ k)⁻¹ * (g * e * g⁻¹) = z ^ k * z⁻¹ := by
        have h4 : (g * e * g⁻¹) * z = e ^ k * z ^ k := by rw [← h1, ← hk, h2]
        calc (e ^ k)⁻¹ * (g * e * g⁻¹) = (e ^ k)⁻¹ * ((g * e * g⁻¹) * z) * z⁻¹ := by group
          _ = (e ^ k)⁻¹ * (e ^ k * z ^ k) * z⁻¹ := by rw [h4]
          _ = z ^ k * z⁻¹ := by group
      have hL' : (e ^ k)⁻¹ * (g * e * g⁻¹) ∈ L :=
        L.mul_mem (L.inv_mem (L.zpow_mem heL k)) (L.mul_mem (L.mul_mem hgL heL) (L.inv_mem hgL))
      have hC' : (e ^ k)⁻¹ * (g * e * g⁻¹) ∈ C := by
        rw [h3]
        exact C.mul_mem (C.zpow_mem hdC k) (C.inv_mem hdC)
      have h5 := hLC _ hL' hC'
      have h6 : g * e * g⁻¹ = e ^ k := by
        calc g * e * g⁻¹ = e ^ k * ((e ^ k)⁻¹ * (g * e * g⁻¹)) := by group
          _ = e ^ k := by rw [h5, mul_one]
      rw [h6]
      exact Subgroup.zpow_mem_zpowers e k
    exact hne (mem_normalizer_zpowers_of_conj (hconj n hnL hnd)
      (hconj n⁻¹ (L.inv_mem hnL) (Subgroup.inv_mem _ hnd)))

end Core

@[expose] def InvAt (S : Type) [Group S] (x : S) : Prop :=
  ∀ B : Subgroup S, CFSG.Assembly.IsElemAbelian 3 B → x ∈ B →
    ∃ t : S, t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ b ∈ B, t * b = b * t

@[expose] def ExtAt (S : Type) [Group S] (x : S) : Prop :=
  ∃ s : S, s * x = x * s ∧ s ^ 3 = 1 ∧ s ∉ Subgroup.zpowers x

@[expose] def MoveAt (S : Type) [Group S] (x : S) : Prop :=
  ∀ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 → x ∈ E →
    (∀ F : Subgroup S, CFSG.Assembly.IsElemAbelian 3 F → E ≤ F → F = E) →
    ∃ n ∈ Subgroup.normalizer (E : Set S), n ∉ Subgroup.normalizer (Subgroup.zpowers x : Set S)

section Transport

variable {G : Type} [Group G] [Finite G] {S : Type} [Group S] {L : Subgroup G} (φ : L ≃* S)

theorem inv_of_invAt {e : G} (he : e ∈ L) (h : InvAt S (φ ⟨e, he⟩)) :
    ∀ B : Subgroup G, B ≤ L → CFSG.Assembly.IsElemAbelian 3 B → e ∈ B →
      ∃ t ∈ L, t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ b ∈ B, t * b = b * t := by
  intro B hBL hB heB
  obtain ⟨t', ht'1, ht'2, ht'B⟩ := h ((B.subgroupOf L).map φ.toMonoidHom)
    (isElemAbelian_map _ (isElemAbelian_comap L.subtype L.subtype_injective hB))
    ⟨⟨e, he⟩, heB, rfl⟩
  refine ⟨(φ.symm t' : G), (φ.symm t').2, ?_, ?_, ?_⟩
  · intro h1
    apply ht'1
    have h2 : φ.symm t' = 1 := Subtype.ext h1
    rw [← φ.apply_symm_apply t', h2, map_one]
  · have h2 : φ.symm t' ^ 2 = 1 := by rw [← map_pow, ht'2, map_one]
    have h3 := congrArg Subtype.val h2
    simpa using h3
  · intro b hb
    have h1 := ht'B (φ ⟨b, hBL hb⟩) ⟨⟨b, hBL hb⟩, hb, rfl⟩
    have h2 : φ.symm t' * ⟨b, hBL hb⟩ = ⟨b, hBL hb⟩ * φ.symm t' := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h1
    exact congrArg Subtype.val h2

theorem ext_of_extAt {e : G} (he : e ∈ L) (h : ExtAt S (φ ⟨e, he⟩)) :
    ∃ s ∈ L, s * e = e * s ∧ s ^ 3 = 1 ∧ s ∉ Subgroup.zpowers e := by
  obtain ⟨s', hs'e, hs'3, hs'z⟩ := h
  refine ⟨(φ.symm s' : G), (φ.symm s').2, ?_, ?_, ?_⟩
  · have h2 : φ.symm s' * ⟨e, he⟩ = ⟨e, he⟩ * φ.symm s' := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hs'e
    exact congrArg Subtype.val h2
  · have h2 : φ.symm s' ^ 3 = 1 := by rw [← map_pow, hs'3, map_one]
    have h3 := congrArg Subtype.val h2
    simpa using h3
  · intro hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    apply hs'z
    have h1 : (⟨e, he⟩ : L) ^ k = φ.symm s' := Subtype.ext (by simpa using hk)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow, h1, MulEquiv.apply_symm_apply]⟩

theorem move_of_moveAt {e : G} (he : e ∈ L) (h : MoveAt S (φ ⟨e, he⟩)) :
    ∀ E : Subgroup G, E ≤ L → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 → e ∈ E →
      (∀ F : Subgroup G, F ≤ L → CFSG.Assembly.IsElemAbelian 3 F → E ≤ F → F = E) →
      ∃ n ∈ L, n ∈ Subgroup.normalizer (E : Set G) ∧
        n ∉ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
  intro E hEL hE hE9 heE hEmax
  set E' := (E.subgroupOf L).map φ.toMonoidHom with hE'
  have hE'el : CFSG.Assembly.IsElemAbelian 3 E' :=
    isElemAbelian_map _ (isElemAbelian_comap L.subtype L.subtype_injective hE)
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE9]
  have heE' : φ ⟨e, he⟩ ∈ E' := ⟨⟨e, he⟩, heE, rfl⟩
  have hE'max : ∀ F' : Subgroup S, CFSG.Assembly.IsElemAbelian 3 F' → E' ≤ F' → F' = E' := by
    intro F' hF' hEF'
    set F := (F'.map φ.symm.toMonoidHom).map L.subtype with hF
    have hFL : F ≤ L := Subgroup.map_subtype_le _
    have hFel : CFSG.Assembly.IsElemAbelian 3 F :=
      isElemAbelian_map _ (isElemAbelian_map _ hF')
    have hEF : E ≤ F := fun x hx =>
      ⟨⟨x, hEL hx⟩, ⟨φ ⟨x, hEL hx⟩, hEF' ⟨⟨x, hEL hx⟩, hx, rfl⟩, φ.symm_apply_apply _⟩, rfl⟩
    have hFE := hEmax F hFL hFel hEF
    refine le_antisymm ?_ hEF'
    intro y hy
    have hyF : ((φ.symm y : L) : G) ∈ F := ⟨φ.symm y, ⟨y, hy, rfl⟩, rfl⟩
    rw [hFE] at hyF
    exact ⟨φ.symm y, hyF, by simp⟩
  obtain ⟨n', hn', hn'z⟩ := h E' hE'el hE'9 heE' hE'max
  rw [hE', ← Subgroup.map_equiv_normalizer_eq] at hn'
  obtain ⟨m, hm, rfl⟩ := hn'
  refine ⟨(m : G), m.2, mem_normalizer_of_subgroupOf hEL hm, fun hmz => hn'z ?_⟩
  have hZc : (Subgroup.zpowers (⟨e, he⟩ : L)).map φ.toMonoidHom =
      Subgroup.zpowers (φ ⟨e, he⟩) := MonoidHom.map_zpowers _ _
  rw [← hZc, ← Subgroup.map_equiv_normalizer_eq]
  refine ⟨m, ?_, rfl⟩
  rw [← zpowers_subgroupOf he]
  exact mem_normalizer_subgroupOf (Subgroup.zpowers_le.mpr he) hmz

end Transport

@[expose] def SylNineMove (S : Type) [Group S] : Prop :=
  ∃ E₀ : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 9 ∧
    ¬ 27 ∣ Nat.card S ∧ (∃ t : S, t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ x ∈ E₀, t * x = x * t) ∧
    ∀ s ∈ E₀, s ≠ 1 → ∃ n ∈ Subgroup.normalizer (E₀ : Set S),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S)

theorem SylNineMove.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : SylNineMove Y) : SylNineMove X := by
  obtain ⟨E₀, hE₀, hE₀9, h27, ⟨t, ht1, ht2, htE⟩, hmv⟩ := h
  refine ⟨E₀.map e.symm.toMonoidHom, isElemAbelian_map _ hE₀,
    by rw [Subgroup.card_map_of_injective e.symm.injective, hE₀9],
    by rwa [Nat.card_congr e.toEquiv], ⟨e.symm t, ?_, ?_, ?_⟩, ?_⟩
  · rw [Ne, map_eq_one_iff _ e.symm.injective]
    exact ht1
  · rw [← map_pow, ht2, map_one]
  · rintro _ ⟨x, hx, rfl⟩
    change e.symm t * e.symm x = e.symm x * e.symm t
    rw [← map_mul, ← map_mul, htE x hx]
  · rintro _ ⟨s, hs, rfl⟩ hs1
    have hs1' : s ≠ 1 := by
      rintro rfl
      exact hs1 (map_one _)
    obtain ⟨n, hn, hns⟩ := hmv s hs hs1'
    refine ⟨e.symm n, ?_, ?_⟩
    · rw [← Subgroup.map_equiv_normalizer_eq]
      exact ⟨n, hn, rfl⟩
    · intro hn'
      apply hns
      have hZ : (Subgroup.zpowers s).map e.symm.toMonoidHom =
          Subgroup.zpowers (e.symm.toMonoidHom s) := MonoidHom.map_zpowers _ s
      rw [← hZ, ← Subgroup.map_equiv_normalizer_eq] at hn'
      obtain ⟨m, hm, hmn⟩ := hn'
      rwa [e.symm.injective hmn] at hm

theorem at_of_sylNineMove {S : Type} [Group S] [Finite S] (h : SylNineMove S) (x : S)
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) : InvAt S x ∧ ExtAt S x ∧ MoveAt S x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₀, hE₀, hE₀9, h27, ⟨t, ht1, ht2, htE⟩, hmv⟩ := h
  have hfac : (Nat.card S).factorization 3 = 2 := by
    obtain ⟨m, hm⟩ : 9 ∣ Nat.card S := hE₀9 ▸ Subgroup.card_subgroup_dvd_card E₀
    refine KFacts.KS21.factorization_three_eq (m := 2) (k := m) (by rw [hm]; norm_num) ?_
    rintro ⟨j, rfl⟩
    exact h27 ⟨j, by rw [hm]; ring⟩
  let P₀ : Sylow 3 S := Sylow.ofCard E₀ (by rw [hE₀9, hfac]; norm_num)
  have hconj : ∀ B : Subgroup S, IsPGroup 3 B →
      ∃ g : S, B.map (MulAut.conj g).toMonoidHom ≤ E₀ := by
    intro B hB
    obtain ⟨Q, hBQ⟩ := hB.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P₀ Q
    exact ⟨g⁻¹, KFacts.KS21.map_conj_inv_le hg hBQ⟩
  have hE₀c : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE₀.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro B hB _
    obtain ⟨g, hg⟩ := hconj B (KFacts.KS21.isPGroup_of_isElemAbelian hB)
    refine ⟨g⁻¹ * t * g, ?_, ?_, ?_⟩
    · intro h1
      apply ht1
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · calc (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g := by rw [sq, sq]; group
        _ = 1 := by rw [ht2]; group
    · intro b hb
      have hgb : g * b * g⁻¹ ∈ E₀ := hg ⟨b, hb, rfl⟩
      have h1 := htE _ hgb
      calc g⁻¹ * t * g * b = g⁻¹ * (t * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * b * g⁻¹) * t) * g := by rw [h1]
        _ = b * (g⁻¹ * t * g) := by group
  · obtain ⟨g, hg⟩ := hconj (Subgroup.zpowers x) (KFacts.KS21.isPGroup_of_isElemAbelian
      (CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hx3))
    have hgx : g * x * g⁻¹ ∈ E₀ := hg ⟨x, Subgroup.mem_zpowers x, rfl⟩
    have hgx3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
    have hgx1 : g * x * g⁻¹ ≠ 1 := by
      intro h1
      apply hx1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have hlt : Subgroup.zpowers (g * x * g⁻¹) < E₀ := by
      refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hgx) ?_
      intro heq
      have h1 : Nat.card (Subgroup.zpowers (g * x * g⁻¹)) = Nat.card E₀ := by rw [heq]
      rw [Nat.card_zpowers, hE₀9, orderOf_eq_prime hgx3 hgx1] at h1
      norm_num at h1
    obtain ⟨s₀, hs₀E, hs₀z⟩ := SetLike.exists_of_lt hlt
    refine ⟨g⁻¹ * s₀ * g, ?_, ?_, ?_⟩
    · have h1 := hE₀c s₀ hs₀E _ hgx
      calc g⁻¹ * s₀ * g * x = g⁻¹ * (s₀ * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * s₀) * g := by rw [h1]
        _ = x * (g⁻¹ * s₀ * g) := by group
    · calc (g⁻¹ * s₀ * g) ^ 3 = g⁻¹ * s₀ ^ 3 * g := by rw [pow_three, pow_three]; group
        _ = 1 := by rw [hE₀.2 s₀ hs₀E]; group
    · intro hz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
      apply hs₀z
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [conj_zpow, hk]
      group
  · intro E hE hE9 hxE _
    obtain ⟨g, hg⟩ := hconj E (KFacts.KS21.isPGroup_of_isElemAbelian hE)
    have hgE : E.map (MulAut.conj g).toMonoidHom = E₀ := Subgroup.eq_of_le_of_card_ge hg
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE9, hE₀9])
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id S := by
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    have hEeq : E = E₀.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [← hgE, Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [hEeq] at hxE ⊢
    exact Ronan148R.moves_map (MulAut.conj g⁻¹) hmv x hxE hx1

section Row

theorem row427Cent_of_at
    {S : Type} [Group S] (h3 : NoThreeCover S) (hcube : CubeInner S)
    (hat : ∀ x : S, x ≠ 1 → x ^ 3 = 1 → InvAt S x ∧ ExtAt S x ∧ MoveAt S x) :
    Row427Cent S := by
  intro G _ _ hG A hA hEF hθ L hL ⟨eL⟩ d hdA _ hN hLd _ _ _ hCA
  have hZ : Subgroup.center L = ⊥ := center_eq_bot_of_noThreeCover h3 hθ hL eL
  let φ : L ≃* S := (RonanK429.quotCenterEquivOfEqBot hZ).trans eL
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
      (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  have hφ : ∀ e (he : e ∈ L), e ≠ 1 → e ^ 3 = 1 →
      InvAt S (φ ⟨e, he⟩) ∧ ExtAt S (φ ⟨e, he⟩) ∧ MoveAt S (φ ⟨e, he⟩) := by
    intro e he he1 he3
    refine hat _ ?_ ?_
    · rw [Ne, map_eq_one_iff _ φ.injective]
      exact fun h => he1 (congrArg Subtype.val h)
    · rw [← map_pow]
      have h1 : (⟨e, he⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using he3)
      rw [h1, map_one]
  exact false_of_inner_cent hA hEF hZ (cubeInner_of_mulEquiv φ hcube) hAN hdA hN hLd hCA
    (fun e he he1 he3 _ => inv_of_invAt φ he (hφ e he he1 he3).1)
    (fun e he he1 he3 _ => ext_of_extAt φ he (hφ e he he1 he3).2.1)
    (fun e he he1 he3 _ => move_of_moveAt φ he (hφ e he he1 he3).2.2)

theorem rowOf427Cent_of_sylNineMove
    {X : Type} [Group X] (h3 : NoThreeCover X)
    (hcube : CubeInner X) (hX : SylNineMove X) : RowOf427Cent X :=
  fun S _ _ _ _ ⟨e⟩ => row427Cent_of_at
    (HardMathSupport.Solomon.Coordinator.LieComp.NoThreeCover.of_mulEquiv e h3)
    (cubeInner_of_mulEquiv e hcube) (at_of_sylNineMove (hX.of_mulEquiv e))

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
