module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import Mathlib.GroupTheory.Index
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumannTools
import CFSG.Quasithin.Vol2.Ch12Sec8OneFlag
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
import CFSG.Quasithin.Background.F9Basic
import CFSG.Quasithin.H13.StatementsVocab

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma kgLangS1EIndexAux_prod_range_const {G : Type*} [Monoid G] (x : G) (n : ℕ) :
    ((List.range n).map fun _ => x).prod = x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih]
      simp [pow_succ]

private lemma kgLangS1EIndexAux_sum_range_odd (m : ℕ) :
    (List.range (2 * m + 1)).sum = m * (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, List.range_succ,
        List.range_succ, List.sum_append, List.sum_append]
      simp only [List.sum_singleton]
      rw [ih]
      ring

private lemma kgLangS1EIndexAux_prod_range_cz {K : Type*} [Group K] (c z : K)
    (hz : z ∈ Subgroup.center K) (n : ℕ) :
    ((List.range n).map fun i => c * z ^ i).prod = c ^ n * z ^ (List.range n).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, List.sum_append]
      simp only [List.map_singleton, List.prod_singleton, List.sum_singleton]
      have hcomm : ∀ a : ℕ, ∀ b : K, z ^ a * b = b * z ^ a := fun a b =>
        (Subgroup.mem_center_iff.mp ((Subgroup.center K).pow_mem hz a) b).symm
      calc
        c ^ n * z ^ (List.range n).sum * (c * z ^ n)
            = c ^ n * (z ^ (List.range n).sum * c) * z ^ n := by
              simp only [mul_assoc]
        _ = c ^ n * (c * z ^ (List.range n).sum) * z ^ n := by
              rw [hcomm (List.range n).sum c]
        _ = (c ^ n * c) * (z ^ (List.range n).sum * z ^ n) := by
              simp only [mul_assoc]
        _ = c ^ (n + 1) * z ^ ((List.range n).sum + n) := by
              rw [pow_succ, pow_add]

private lemma kgLangS1EIndexAux_prod_range_telescope {G : Type*} [Group G] (f : ℕ → G)
    (n : ℕ) :
    ((List.range n).map fun i => f i * (f (i + 1))⁻¹).prod = f 0 * (f n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih]
      simp only [List.map_singleton, List.prod_singleton]
      calc
        (f 0 * (f n)⁻¹) * (f n * (f (n + 1))⁻¹)
            = f 0 * ((f n)⁻¹ * (f n * (f (n + 1))⁻¹)) := by
              simp only [mul_assoc]
        _ = f 0 * (((f n)⁻¹ * f n) * (f (n + 1))⁻¹) := by
              simp only [mul_assoc]
        _ = f 0 * (f (n + 1))⁻¹ := by
              rw [inv_mul_cancel, one_mul]

private lemma kgLangS1EIndexAux_kgInducedAut_apply_mk {K R : Type*} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (α : MulAut K) (k : K) :
    kgInducedAut θ α (θ (QuotientGroup.mk k)) = θ (QuotientGroup.mk (α k)) := by
  change (MulAut.congr θ) ((centerQuotAut K) α) (θ (QuotientGroup.mk k)) =
    θ (QuotientGroup.mk (α k))
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  rfl

theorem kgLangS1E_index_lang {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G]
    (β : MulAut G) (N : Subgroup G) (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hβN : ∀ g, β g ∈ N ↔ g ∈ N)
    (hH90 : ∀ c ∈ N, ((List.range p).map fun i => (β ^ i) c).prod = 1 →
      ∃ s ∈ N, c = s⁻¹ * β s)
    (R₀ : Subgroup G) (hβR₀ : ∀ g ∈ R₀, β g ∈ R₀) (hidx : R₀.relIndex N ≤ p)
    (E : Subgroup G) (hEN : E ≤ N) (hEp : ∀ x ∈ E, x ^ p = 1) (hEβ : ∀ x ∈ E, β x = x)
    (hEcard : p ^ 2 ≤ Nat.card E) :
    ∃ s ∈ N ⊓ R₀, s⁻¹ * β s ≠ 1 ∧ s⁻¹ * β s ∈ E := by
  letI : CommGroup N := CommGroup.mk fun a b => Subtype.ext (hNab a a.2 b b.2)
  let βN : N →* N :=
    { toFun := fun s => ⟨β (s : G), (hβN (s : G)).mpr s.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro a b; apply Subtype.ext; simp [map_mul] }
  let δ : N →* N :=
    { toFun := fun s => s⁻¹ * βN s
      map_one' := by change (1 : N)⁻¹ * βN 1 = 1; simp
      map_mul' := by
        intro a b
        change (a * b)⁻¹ * βN (a * b) = (a⁻¹ * βN a) * (b⁻¹ * βN b)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  let K : Subgroup N := R₀.subgroupOf N
  have hδK : K.map δ ≤ K := by
    rintro y ⟨x, hx, rfl⟩
    have hxR : (x : G) ∈ R₀ := by
      change x ∈ R₀.subgroupOf N at hx
      exact Subgroup.mem_subgroupOf.mp hx
    change δ x ∈ R₀.subgroupOf N
    rw [Subgroup.mem_subgroupOf]
    change (x : G)⁻¹ * β (x : G) ∈ R₀
    exact R₀.mul_mem (R₀.inv_mem hxR) (hβR₀ (x : G) hxR)
  let δK : Subgroup N := K.map δ
  have hδKle : δK ≤ δ.range := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, rfl⟩
  let δKG : Subgroup G := δK.map N.subtype
  let Rδ : Subgroup G := δ.range.map N.subtype
  have hδKGle : δKG ≤ Rδ := Subgroup.map_mono hδKle
  have hδKidx : δK.relIndex δ.range ≤ p := by
    have hdvd := CFSG.Quasithin.H13.relIndex_map_dvd δ (le_top : K ≤ ⊤)
    rw [Subgroup.map_top] at hdvd
    have hKidx : K.relIndex (⊤ : Subgroup N) ≤ p := by
      rw [Subgroup.relIndex_top_right]
      change (R₀.subgroupOf N).index ≤ p
      exact hidx
    have hpos : 0 < K.relIndex (⊤ : Subgroup N) :=
      Nat.pos_of_ne_zero
        (CFSG.QuasithinUnique.Setup.Campbell.relIndex_ne_zero_of_finite K ⊤)
    exact (Nat.le_of_dvd hpos hdvd).trans hKidx
  have hδKGidx : δKG.relIndex Rδ ≤ p := by
    rw [show δKG.relIndex Rδ = δK.relIndex δ.range from
      Subgroup.relIndex_map_map_of_injective δK δ.range N.subtype_injective]
    exact hδKidx
  have hEβpow : ∀ x ∈ E, ∀ i : ℕ, (β ^ i) x = x := by
    intro x hx i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', MulAut.mul_apply, ih, hEβ x hx]
  have hEδR : E ≤ Rδ := by
    intro x hx
    have hxN : x ∈ N := hEN hx
    have hconst : ((List.range p).map fun i => (β ^ i) x)
        = ((List.range p).map fun _ => x) :=
      List.map_congr_left fun i _ => hEβpow x hx i
    have hnorm : ((List.range p).map fun i => (β ^ i) x).prod = 1 := by
      rw [hconst, kgLangS1EIndexAux_prod_range_const, hEp x hx]
    obtain ⟨s, hsN, hs⟩ := hH90 x hxN hnorm
    refine ⟨δ ⟨s, hsN⟩, ⟨⟨s, hsN⟩, rfl⟩, ?_⟩
    rw [hs]
    rfl
  let D : Subgroup G := E ⊓ δKG
  have hEidx : D.relIndex E ≤ p := by
    have htemp := CFSG.QuasithinUnique.Setup.Campbell.relIndex_inf_le_of_le hEδR δKG
    rw [inf_eq_right.mpr hδKGle] at htemp
    exact htemp.trans hδKGidx
  have hcardD : p ≤ Nat.card D := by
    have hmul := Subgroup.relIndex_mul_card D E
    have hDE : D ⊓ E = D := inf_eq_left.mpr (show D ≤ E from inf_le_left)
    rw [hDE] at hmul
    have hp2 : p * p ≤ Nat.card D * p := by
      have hEcard' : p * p ≤ Nat.card E := by simpa [pow_two] using hEcard
      calc
        p * p ≤ Nat.card E := hEcard'
        _ = D.relIndex E * Nat.card D := hmul.symm
        _ ≤ p * Nat.card D := Nat.mul_le_mul_right _ hEidx
        _ = Nat.card D * p := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right hp2 hp.pos
  have hDne : D ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card D = 1 := by rw [hbot]; simp
    have h2 : 2 ≤ Nat.card D := hp.two_le.trans hcardD
    omega
  obtain ⟨⟨x, hxD⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have hxne : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxδKG : x ∈ δKG := (Subgroup.mem_inf.mp hxD).2
  obtain ⟨y, hyδK, hyx⟩ := Subgroup.mem_map.mp hxδKG
  obtain ⟨z, hzK, hzy⟩ := Subgroup.mem_map.mp hyδK
  have hzR : (z : G) ∈ R₀ := by
    rwa [Subgroup.mem_subgroupOf] at hzK
  have hzx : (z : G)⁻¹ * β (z : G) = x := by
    have h1 : ((δ z : N) : G) = x := by
      rw [hzy]
      exact hyx
    simpa [δ, βN] using h1
  refine ⟨(z : G), ⟨z.2, hzR⟩, ?_, ?_⟩
  · rw [hzx]
    exact hxne
  · rw [hzx]
    exact (Subgroup.mem_inf.mp hxD).1

private lemma kgLangS1EIndexAux_mul_mul_inv {G : Type*} [Group G] (c z : G)
    (hz : z⁻¹ * c = c * z⁻¹) : c * (c * z)⁻¹ = z⁻¹ := by
  rw [mul_inv_rev, ← mul_assoc, ← hz, mul_assoc, mul_inv_cancel, mul_one]

theorem kgLangS1E_central_error {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K]
    (A : Subgroup (MulAut K)) (hA : IsElemAbelian p A) (B₀ : Set (MulAut K)) (hB₀A : B₀ ⊆ A)
    {α₀ : MulAut K} (hα₀ : α₀ ∈ A) (hdec : ∀ α ∈ A, ∃ β ∈ B₀, ∃ j : ℕ, α = β * α₀ ^ j)
    (hZp : ∀ z ∈ Subgroup.center K, z ^ p = 1)
    (hZA : ∀ α ∈ A, ∀ z ∈ Subgroup.center K, α z = z)
    {k : K} (hk : ∀ β ∈ B₀, β k = k) (hc : k * (α₀ k)⁻¹ ≠ 1)
    (hcz : (k * (α₀ k)⁻¹)⁻¹ * α₀ (k * (α₀ k)⁻¹) ∈ Subgroup.center K) :
    ∃ k' e : K, e ≠ 1 ∧ e ^ p = 1 ∧ (∀ α ∈ A, α e = e) ∧ (∀ β ∈ B₀, β k' = k') ∧
      k' * (α₀ k')⁻¹ = e := by
  let c : K := k * (α₀ k)⁻¹
  let z : K := c⁻¹ * α₀ c
  have hzc : z ∈ Subgroup.center K := hcz
  have hαp : α₀ ^ p = 1 := hA.2 α₀ hα₀
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hαc : α₀ c = c * z := by
    dsimp [z]
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hαz : α₀ z = z := hZA α₀ hα₀ z hzc
  have hpow : ∀ i : ℕ, (α₀ ^ i) c = c * z ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, hαc, map_pow, hαz, mul_assoc,
          ← pow_succ']
  have hprod : ((List.range p).map fun i => (α₀ ^ i) c).prod
      = c ^ p * z ^ (List.range p).sum := by
    rw [show (fun i => (α₀ ^ i) c) = (fun i => c * z ^ i) from funext hpow]
    exact kgLangS1EIndexAux_prod_range_cz c z hzc p
  have htel : ((List.range p).map fun i => (α₀ ^ i) c).prod = 1 := by
    have hlist : ((List.range p).map fun i => (α₀ ^ i) c)
        = ((List.range p).map fun i => (α₀ ^ i) k * ((α₀ ^ (i + 1)) k)⁻¹) := by
      apply List.map_congr_left
      intro i _
      simp only [c, map_mul, map_inv, pow_succ, MulAut.mul_apply]
    rw [hlist, kgLangS1EIndexAux_prod_range_telescope (fun i => (α₀ ^ i) k) p]
    simp [hαp]
  have hzsum : z ^ (List.range p).sum = 1 := by
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    have hsum : (List.range p).sum = m * p := by
      rw [hm, kgLangS1EIndexAux_sum_range_odd]
    rw [hsum, mul_comm m p, pow_mul, hZp z hzc, one_pow]
  have hcp : c ^ p = 1 := by
    have h := hprod
    rw [htel, hzsum, mul_one] at h
    exact h.symm
  have hcfixB : ∀ β ∈ B₀, β c = c := by
    intro β hβ
    have hβα₀ : β * α₀ = α₀ * β := hcommA β (hB₀A hβ) α₀ hα₀
    have hβk : β k = k := hk β hβ
    have hβαk : β (α₀ k) = α₀ k := by
      rw [← MulAut.mul_apply, hβα₀, MulAut.mul_apply, hβk]
    dsimp [c]
    rw [map_mul, map_inv, hβk, hβαk]
  rcases eq_or_ne z 1 with hz1 | hz1
  · refine ⟨k, c, hc, hcp, ?_, hk, rfl⟩
    have hcfixα₀ : α₀ c = c := by rw [hαc, hz1, mul_one]
    have hα₀pow : ∀ n : ℕ, (α₀ ^ n) c = c := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hcfixα₀]
    intro α hα
    obtain ⟨β, hβ, j, rfl⟩ := hdec α hα
    have hβc : β c = c := hcfixB β hβ
    have hα₀c : (α₀ ^ j) c = c := hα₀pow j
    rw [MulAut.mul_apply, hα₀c, hβc]
  · refine ⟨c, z⁻¹, ?_, ?_, ?_, ?_, ?_⟩
    · intro hz
      apply hz1
      simpa using congrArg Inv.inv hz
    · rw [inv_pow, hZp z hzc, inv_one]
    · intro α hα
      exact hZA α hα z⁻¹ (Subgroup.inv_mem (Subgroup.center K) hzc)
    · intro β hβ
      exact hcfixB β hβ
    · have hzc' : z⁻¹ * c = c * z⁻¹ :=
        (Subgroup.mem_center_iff.mp (Subgroup.inv_mem (Subgroup.center K) hzc) c).symm
      rw [hαc]
      exact kgLangS1EIndexAux_mul_mul_inv c z hzc'

theorem kgLangS1E_of_model_index {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K R G : Type} [Group K]
    [Group R] [Group G] [Finite G]
    (θ : K ⧸ Subgroup.center K ≃* R) (hZp : ∀ z ∈ Subgroup.center K, z ^ p = 1)
    (J : Subgroup (MulAut R)) (A : Subgroup (MulAut K)) (hA : IsElemAbelian p A)
    (hZA : ∀ α ∈ A, ∀ z ∈ Subgroup.center K, α z = z)
    (α₀ : MulAut K) (hα₀ : α₀ ∈ A)
    (hdec : ∀ α ∈ A, ∃ β ∈ A, kgInducedAut θ β ∈ J ∧ ∃ j : ℕ, α = β * α₀ ^ j)
    (ι : R →* G) (hι : Function.Injective ι)
    (β : MulAut G) (hβι : ∀ r, ι (kgInducedAut θ α₀ r) = β (ι r))
    (N : Subgroup G) (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hβN : ∀ g, β g ∈ N ↔ g ∈ N)
    (hH90 : ∀ c ∈ N, ((List.range p).map fun i => (β ^ i) c).prod = 1 →
      ∃ s ∈ N, c = s⁻¹ * β s)
    (hidx : ι.range.relIndex N ≤ p)
    (h : MulAut K → G)
    (hh : ∀ α ∈ A, kgInducedAut θ α ∈ J → h α ∈ N ∧ h α ^ p = 1 ∧ β (h α) = h α ∧
      ∀ r, ι (kgInducedAut θ α r) = h α * ι r * (h α)⁻¹)
    (hne : ∀ α ∈ A, kgInducedAut θ α ∈ J → α ≠ 1 → h α ≠ 1)
    (hmul : ∀ α ∈ A, ∀ α' ∈ A, kgInducedAut θ α ∈ J → kgInducedAut θ α' ∈ J →
      h (α * α') = h α * h α')
    (hcard : p ^ 2 ≤ Nat.card {α : MulAut K // α ∈ A ∧ kgInducedAut θ α ∈ J})
    (hlift : ∀ α ∈ A, kgInducedAut θ α ∈ J → ∀ r : R, ι r ∈ N →
      ∀ k : K, θ (QuotientGroup.mk k) = r → α k = k) :
    ∃ k e : K, e ≠ 1 ∧ e ^ p = 1 ∧ (∀ α ∈ A, α e = e) ∧
      (∀ α ∈ A, kgInducedAut θ α ∈ J → α k = k) ∧ k * (α₀ k)⁻¹ = e := by
  let A₀ : Subgroup (MulAut K) := A ⊓ J.comap (kgInducedAut θ)
  have hmemA₀ : ∀ α : MulAut K, α ∈ A₀ ↔ α ∈ A ∧ kgInducedAut θ α ∈ J := by
    intro α
    simp [A₀]
  have honeJ : kgInducedAut θ (1 : MulAut K) ∈ J := by simp
  have hmul11 := hmul 1 A.one_mem 1 A.one_mem honeJ honeJ
  have hh1 : h 1 = 1 := by
    have h2 : h 1 * 1 = h 1 * h 1 := by
      rw [mul_one]
      simpa using hmul11
    exact (mul_left_cancel h2).symm
  let φ : A₀ →* G :=
    { toFun := fun α => h α
      map_one' := hh1
      map_mul' := by
        intro α α'
        exact hmul (α : MulAut K) α.2.1 (α' : MulAut K) α'.2.1 α.2.2 α'.2.2 }
  have hinj : Function.Injective φ := by
    intro α α' hαα'
    apply Subtype.ext
    have hdφ : φ (α * α'⁻¹) = 1 := by
      rw [map_mul, map_inv, hαα', mul_inv_cancel]
    have hd1 : α * α'⁻¹ = 1 := by
      by_contra hne1
      have hdA' : (α * α'⁻¹).val ∈ A := (α * α'⁻¹).2.1
      have hdJ : kgInducedAut θ (α * α'⁻¹).val ∈ J := (α * α'⁻¹).2.2
      have hne1' : (α * α'⁻¹).val ≠ 1 := fun h => hne1 (Subtype.ext h)
      have hne' : h (α * α'⁻¹).val ≠ 1 := hne _ hdA' hdJ hne1'
      exact hne' (by simpa [φ] using hdφ)
    have hd1val : α.val * (α'.val)⁻¹ = 1 := by
      simpa using congrArg Subtype.val hd1
    calc
      α.val = (α.val * (α'.val)⁻¹) * α'.val := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = α'.val := by rw [hd1val, one_mul]
  let E : Subgroup G := (⊤ : Subgroup A₀).map φ
  have hEN : E ≤ N := by
    rintro x ⟨α, -, rfl⟩
    exact (hh α α.2.1 α.2.2).1
  have hEp : ∀ x ∈ E, x ^ p = 1 := by
    rintro x ⟨α, -, rfl⟩
    exact (hh α α.2.1 α.2.2).2.1
  have hEβ : ∀ x ∈ E, β x = x := by
    rintro x ⟨α, -, rfl⟩
    exact (hh α α.2.1 α.2.2).2.2.1
  have hcardE : p ^ 2 ≤ Nat.card E := by
    have hEc : Nat.card E = Nat.card A₀ := by
      dsimp [E]
      rw [Subgroup.card_map_of_injective hinj, Subgroup.card_top]
    rw [hEc]
    simpa [A₀] using hcard
  have hβR₀ : ∀ g ∈ ι.range, β g ∈ ι.range := by
    rintro g ⟨r, rfl⟩
    exact ⟨kgInducedAut θ α₀ r, hβι r⟩
  obtain ⟨s, hs, hsne, hsE⟩ :=
    kgLangS1E_index_lang hp β N hNab hβN hH90 ι.range hβR₀ hidx E hEN hEp hEβ hcardE
  obtain ⟨hr₀, hr₀s⟩ := hs.2
  have hιr₀ : ι hr₀ = s := hr₀s
  have hιinv : ι hr₀⁻¹ = s⁻¹ := by rw [map_inv, hιr₀]
  have hsN : s ∈ N := hs.1
  have hsNinv : s⁻¹ ∈ N := N.inv_mem hsN
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (θ.symm hr₀⁻¹)
  have hkθ : θ (QuotientGroup.mk k) = hr₀⁻¹ := by
    rw [hk, MulEquiv.apply_symm_apply]
  have hkfix : ∀ α ∈ A, kgInducedAut θ α ∈ J → α k = k := by
    intro α hα hαJ
    exact hlift α hα hαJ hr₀⁻¹ (by rw [hιinv]; exact hsNinv) k hkθ
  let c : K := k * (α₀ k)⁻¹
  let π : K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπk : π k = hr₀⁻¹ := hkθ
  have hπα : π (α₀ k) = kgInducedAut θ α₀ hr₀⁻¹ := by
    change θ (QuotientGroup.mk (α₀ k)) = kgInducedAut θ α₀ hr₀⁻¹
    rw [← kgLangS1EIndexAux_kgInducedAut_apply_mk θ α₀ k,
      show θ (QuotientGroup.mk k) = hr₀⁻¹ from hkθ]
  have hπc : π c = hr₀⁻¹ * (kgInducedAut θ α₀ hr₀⁻¹)⁻¹ := by
    dsimp [c]
    rw [map_mul, map_inv, hπk, hπα]
  have hθc : θ (QuotientGroup.mk c) = hr₀⁻¹ * (kgInducedAut θ α₀ hr₀⁻¹)⁻¹ :=
    hπc
  have hιθc : ι (θ (QuotientGroup.mk c)) = s⁻¹ * β s := by
    rw [hθc, map_mul, map_inv]
    simp only [hβι, map_inv, inv_inv, hιr₀]
  have hc : c ≠ 1 := by
    intro hc1
    apply hsne
    have h1 : ι (θ (QuotientGroup.mk c)) = 1 := by rw [hc1]; simp
    rw [hιθc] at h1
    exact h1
  have hβe : β (s⁻¹ * β s) = s⁻¹ * β s := by
    obtain ⟨αe, -, hαe⟩ := hsE
    rw [← hαe]
    exact (hh αe αe.2.1 αe.2.2).2.2.1
  have hικ : ι (θ (QuotientGroup.mk (α₀ c))) = s⁻¹ * β s := by
    have h1 : θ (QuotientGroup.mk (α₀ c))
        = kgInducedAut θ α₀ (θ (QuotientGroup.mk c)) :=
      (kgLangS1EIndexAux_kgInducedAut_apply_mk θ α₀ c).symm
    rw [h1, show ι (kgInducedAut θ α₀ (θ (QuotientGroup.mk c)))
        = β (ι (θ (QuotientGroup.mk c))) from hβι _, hιθc, hβe]
  have hπeq : π (α₀ c) = π c := by
    change θ (QuotientGroup.mk (α₀ c)) = θ (QuotientGroup.mk c)
    exact hι (by rw [hικ, hιθc])
  have hmk : QuotientGroup.mk (c⁻¹ * α₀ c) = (1 : K ⧸ Subgroup.center K) := by
    refine θ.injective ?_
    have hker : π (c⁻¹ * α₀ c) = 1 := by
      rw [map_mul, map_inv, hπeq, inv_mul_cancel]
    rw [map_one]
    exact hker
  have hcz : c⁻¹ * α₀ c ∈ Subgroup.center K :=
    (QuotientGroup.eq_one_iff (c⁻¹ * α₀ c)).mp hmk
  let B₀ : Set (MulAut K) := {β | β ∈ A ∧ kgInducedAut θ β ∈ J}
  have hB₀A : B₀ ⊆ A := fun β hβ => hβ.1
  have hkfixB : ∀ β ∈ B₀, β k = k := fun β hβ => hkfix β hβ.1 hβ.2
  have hdecB : ∀ α ∈ A, ∃ β ∈ B₀, ∃ j : ℕ, α = β * α₀ ^ j := by
    intro α hα
    obtain ⟨β, hβA, hβJ, j, hj⟩ := hdec α hα
    exact ⟨β, ⟨hβA, hβJ⟩, j, hj⟩
  obtain ⟨k', e, hene, hep, hefix, hk'fix, hk'e⟩ :=
    kgLangS1E_central_error hp hp2 A hA B₀ hB₀A hα₀ hdecB hZp hZA hkfixB hc hcz
  refine ⟨k', e, hene, hep, hefix, ?_, hk'e⟩
  intro α hα hαJ
  exact hk'fix α ⟨hα, hαJ⟩

end CFSG.StandardType
