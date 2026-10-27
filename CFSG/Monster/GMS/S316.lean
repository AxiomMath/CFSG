module

public import CFSG.Monster.GMS.S347
public import CFSG.Monster.GMS.Leech.OddLift
public import CFSG.Monster.GMS.Leech.TypeUniqueSystem
public import CFSG.Monster.GMS.Facts.Co1TwoB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Monster.GMS.Leech

theorem two_pow_twelve_le_ncard_co1Fix {g : Co1} (hg : g * g = 1) :
    2 ^ 12 ≤ (co1Fix g).ncard := by
  let T : Module.End (ZMod 2) (Fin 24 → ZMod 2) := co1Act g - (1 : Module.End (ZMod 2) _)
  have hT : ∀ x, T x = co1Act g x + x := fun x => by
    simp only [T, LinearMap.sub_apply, Module.End.one_apply]
    exact Leech.sub_eq_add _ _
  have hker : (co1Fix g) = (LinearMap.ker T : Set (Fin 24 → ZMod 2)) := by
    ext v
    simp only [co1Fix, Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_ker, hT]
    constructor
    · intro h
      rw [h]
      exact CharTwo.add_self_eq_zero v
    · intro h
      exact (eq_neg_of_add_eq_zero_left h).trans (Leech.neg_eq_self v)
  have hle : LinearMap.range T ≤ LinearMap.ker T := by
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, hT, hT, map_add, co1Act_co1Act_of_mul_self_eq_one hg]
    abel_nf
    simp [CharTwo.two_eq_zero]
  have hrk := LinearMap.finrank_range_add_finrank_ker T
  have hmono := Submodule.finrank_mono hle
  rw [Module.finrank_fin_fun] at hrk
  have h12 : 12 ≤ Module.finrank (ZMod 2) (LinearMap.ker T) := by omega
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := FiniteField.pow_finrank_eq_natCard 2 (LinearMap.ker T)
  rw [hker, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, ← hcard]
  exact Nat.pow_le_pow_right (by norm_num) h12


theorem inv_mul_mul_mul_inv_eq_one {K : Type*} [Group K] {a b : K} (h : b * a = a * b) :
    a⁻¹ * b * a * b⁻¹ = 1 := by
  rw [mul_assoc a⁻¹ b a, h]
  group


theorem inv_mul_mul_mul_of_commute {K : Type*} [Group K] {g c : K} (hc : g * c = c * g) (a : K) :
    g⁻¹ * (a * c) * g = g⁻¹ * a * g * c := by
  calc g⁻¹ * (a * c) * g = g⁻¹ * a * (c * g) := by group
    _ = g⁻¹ * a * (g * c) := by rw [hc]
    _ = g⁻¹ * a * g * c := by group


theorem ncard_mul_card_le_of_forall_exists {M V : Type*} [Group M] [Finite M] (act : M → V → V)
    (hact : ∀ g h v, act (g * h) v = act g (act h v)) {K S : Subgroup M} (hSK : S ≤ K) {v : V}
    (hS : ∀ t ∈ S, act t v = v) {F : Set V} (htr : ∀ u ∈ F, ∃ g ∈ K, act g v = u) :
    F.ncard * Nat.card S ≤ Nat.card K := by
  choose g hgK hgv using htr
  let Φ : F × S → K := fun p => ⟨g p.1 p.1.2 * (p.2 : M), K.mul_mem (hgK _ _) (hSK p.2.2)⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨⟨u, hu⟩, t⟩ ⟨⟨u', hu'⟩, t'⟩ he
    have he' : g u hu * (t : M) = g u' hu' * (t' : M) := congrArg Subtype.val he
    have huu : u = u' := by
      have h1 := congrArg (fun m : M => act m v) he'
      simp only [hact, hS _ t.2, hS _ t'.2, hgv] at h1
      exact h1
    subst huu
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel he'))
  have h1 := Nat.card_le_card_of_injective Φ hΦ
  rwa [Nat.card_prod, Nat.card_coe_set_eq] at h1

theorem ncard_le_two_mul_of_coset {H : Type*} [Group H] [Finite H] {P : Set H} {M T : Subgroup H}
    (h1 : ∀ q ∈ P, q ∈ M → q ∈ T) (h2 : ∀ q₀ ∈ P, ∀ q ∈ P, q₀ ∉ M → q ∉ M → q₀⁻¹ * q ∈ T) :
    P.ncard ≤ 2 * Nat.card T := by
  have hsplit : P ⊆ (P ∩ (M : Set H)) ∪ (P \ (M : Set H)) := fun q hq => by
    by_cases hqM : q ∈ M
    · exact Or.inl ⟨hq, hqM⟩
    · exact Or.inr ⟨hq, hqM⟩
  have hA : (P ∩ (M : Set H)).ncard ≤ Nat.card T := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard (fun q hq => h1 q hq.1 hq.2) (Set.toFinite _)
  have hB : (P \ (M : Set H)).ncard ≤ Nat.card T := by
    rcases (P \ (M : Set H)).eq_empty_or_nonempty with he | ⟨q₀, hq₀P, hq₀M⟩
    · rw [he, Set.ncard_empty]
      exact Nat.zero_le _
    · rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      refine Set.ncard_le_ncard_of_injOn (fun q => q₀⁻¹ * q) ?_ ?_ (Set.toFinite _)
      · intro q hq
        exact h2 q₀ hq₀P q hq.1 hq₀M hq.2
      · intro q _ q' _ hqq
        exact mul_left_cancel hqq
  calc P.ncard ≤ ((P ∩ (M : Set H)) ∪ (P \ (M : Set H))).ncard :=
        Set.ncard_le_ncard hsplit (Set.toFinite _)
    _ ≤ (P ∩ (M : Set H)).ncard + (P \ (M : Set H)).ncard := Set.ncard_union_le _ _
    _ ≤ Nat.card T + Nat.card T := Nat.add_le_add hA hB
    _ = 2 * Nat.card T := by ring

variable {G : Type} [Group G] {d₀ : B}

theorem s31_six
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hLI : LeechInvolutionStatement) (h13 : Co1ModuleUniqueness)
    (hI : Co1InvolutionFacts) (h2B : Co1TwoBFacts) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w : G}
    (hw : IsConj z₀ w) (L : LeechSystem w) (x : Subgroup.centralizer ({w} : Set G))
    (hx : orderOf x = 2) : ¬ IsCo1TwoB (L.φ x) := by
  intro hB
  obtain ⟨b, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  set s := L.φ x with hs
  obtain ⟨hcard, htype, htrans, hO2⟩ := h2B s hB
  have hxw : (x : G) ∈ Subgroup.centralizer ({w} : Set G) := x.2
  have hx2 : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxQ : (x : G) ∉ leechQ w := fun hq => by
    have h1 : L.φ x = 1 := (L.φ_ker x).2 hq
    have h2 : orderOf s = 2 := hB.1
    rw [hs, h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hxA : ¬ IsConj a (x : G) := fun hA => by
    have hlift := isLeechCentralLift_of_not_mem_leechQ hSLS hTV hL hG hw hxw hA hxQ
    have h2A := L.isCo1TwoA_phi hI hlift
    have hxx : (⟨(x : G), hlift.mem_centralizer⟩ : Subgroup.centralizer ({w} : Set G)) = x := rfl
    rw [hxx] at h2A
    have h16 := (hI.1 s h2A.1).2 h2A.2
    rw [hB.2.1] at h16
    norm_num at h16
  have hxB : IsConj z₀ (x : G) := (s31_five hSLS hTV hL hG hLI hx2).resolve_left hxA
  obtain ⟨Lx⟩ := exists_leechSystem h13 (hG.2.of_isConj hxB)
  set x' : G := (x : G) with hx'
  have hvecW : ∀ q ∈ leechQ w, q ∈ Subgroup.centralizer ({x'} : Set G) → L.vec q ∈ co1Fix s := by
    intro q hq hqx
    have h1 : x' * q * x'⁻¹ = q := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hqx
      rw [← hqx]; group
    have h2 := L.vec_conj x q hq
    rw [← hx', h1] at h2
    exact h2.symm
  have hW : Nat.card ↥(leechQ w ⊓ Subgroup.centralizer ({x'} : Set G)) ≤ 2 ^ 13 := by
    have hsub : ((leechQ w ⊓ Subgroup.centralizer ({x'} : Set G) : Subgroup G) : Set G) ⊆
        {g : G | g ∈ leechQ w ∧ L.vec g ∈ co1Fix s} := by
      intro q hq
      exact ⟨hq.1, hvecW q hq.1 hq.2⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [L.ncard_preimage, hB.2.1] at h1
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    calc _ ≤ 2 * 2 ^ 12 := h1
      _ = 2 ^ 13 := by norm_num
  have hD : Nat.card ↥(Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x'} : Set G))
      ≤ 2 ^ 13 * (2 ^ 15 * 3 ^ 3 * 5 ^ 2 * 7 * 13) := by
    have h1 := L.card_eq_card_image_mul
      (Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x'} : Set G)) inf_le_left
    have h2 : L.image (Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x'} : Set G))
        ≤ Subgroup.centralizer ({s} : Set Co1) := by
      intro y hy
      obtain ⟨c, hc, rfl⟩ := L.mem_image.1 hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcx : c * x = x * c := Subtype.ext
        (Subgroup.mem_centralizer_singleton_iff.mp hc.2)
      rw [hs, ← map_mul, ← map_mul, hcx]
    have h3 : Nat.card ↥(L.image (Subgroup.centralizer ({w} : Set G) ⊓
        Subgroup.centralizer ({x'} : Set G))) ≤ Nat.card ↥(Subgroup.centralizer ({s} : Set Co1)) :=
      Subgroup.card_le_of_le h2
    have h4 : leechQ w ⊓ (Subgroup.centralizer ({w} : Set G) ⊓
        Subgroup.centralizer ({x'} : Set G)) = leechQ w ⊓ Subgroup.centralizer ({x'} : Set G) := by
      have hQC : leechQ w ≤ Subgroup.centralizer ({w} : Set G) := fun q hq => L.mem_centralizer hq
      rw [← inf_assoc, inf_eq_left.2 hQC]
    rw [h1, h4]
    calc _ ≤ (2 ^ 15 * 3 ^ 3 * 5 ^ 2 * 7 * 13) * 2 ^ 13 := Nat.mul_le_mul (h3.trans hcard) hW
      _ = _ := by ring
  have hwQx : w ∉ leechQ x' := fun hwQ => by
    have hne : w ≠ x' := fun he => hxQ (he ▸ L.z_mem)
    have h1 := card_centralizer_inf_of_mem_leechQ_four hSLS hTV hL hG hxB hwQ hne hw
    rw [inf_comm] at h1
    rw [h1] at hD
    norm_num at hD
  have hwx : w ∈ Subgroup.centralizer ({x'} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hxw).symm
  have hw2 : orderOf w = 2 := h.orderOf_of_isConj hw
  set t := Lx.φ ⟨w, hwx⟩ with ht
  have ht2 : orderOf t = 2 := Lx.orderOf_φ hwx hw2 hwQx
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have hWx : 2 ^ 12 ≤ Nat.card ↥(leechQ x' ⊓ Subgroup.centralizer ({w} : Set G)) := by
    set P : Set G := {g : G | g ∈ leechQ x' ∧ Lx.vec g ∈ co1Fix t} with hP
    have hPcard : 2 ^ 13 ≤ P.ncard := by
      rw [hP, Lx.ncard_preimage]
      have := two_pow_twelve_le_ncard_co1Fix htt
      omega
    have hconj : ∀ q ∈ P, w * q * w⁻¹ = q ∨ w * q * w⁻¹ = q * x' := by
      intro q hq
      have hmem : w * q * w⁻¹ ∈ leechQ x' := Lx.conj_mem' hwx hq.1
      refine Lx.eq_or_eq_mul_z hmem hq.1 ?_
      rw [Lx.vec_conj' hwx hq.1, ← ht]
      exact hq.2
    have hle := ncard_le_two_mul_of_coset (P := P) (M := Subgroup.centralizer ({w} : Set G))
      (T := leechQ x' ⊓ Subgroup.centralizer ({w} : Set G)) (fun q hq hqM => ⟨hq.1, hqM⟩) ?_
    · omega
    intro q₀ hq₀ q hq hq₀M hqM
    have hcomm : ∀ g : G, w * g * w⁻¹ = g → g ∈ Subgroup.centralizer ({w} : Set G) :=
      fun g hg => Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc g * w = w * g * w⁻¹ * w := by rw [hg]
          _ = w * g := by group)
    have hq₀c : w * q₀ * w⁻¹ = q₀ * x' :=
      (hconj q₀ hq₀).resolve_left fun h' => hq₀M (hcomm q₀ h')
    have hqc : w * q * w⁻¹ = q * x' := (hconj q hq).resolve_left fun h' => hqM (hcomm q h')
    have hmQ : q₀⁻¹ * q ∈ leechQ x' := (leechQ x').mul_mem ((leechQ x').inv_mem hq₀.1) hq.1
    refine Subgroup.mem_inf.mpr ⟨hmQ, hcomm _ ?_⟩
    have hx'c : ∀ g ∈ leechQ x', g * x' = x' * g := fun g hg =>
      (Lx.extraspecial.central g hg)
    have e : w * (q₀⁻¹ * q) * w⁻¹ = q₀⁻¹ * q := by
      calc w * (q₀⁻¹ * q) * w⁻¹ = (w * q₀ * w⁻¹)⁻¹ * (w * q * w⁻¹) := by group
        _ = (q₀ * x')⁻¹ * (q * x') := by rw [hq₀c, hqc]
        _ = x'⁻¹ * (q₀⁻¹ * q) * x' := by group
        _ = q₀⁻¹ * q := by
          rw [mul_assoc, hx'c _ hmQ]; group
    exact e
  have hs2 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hB.1, pow_two] at this
  have hfixadd : ∀ v ∈ co1Fix s, ∃ w₀, co1Act s w₀ + w₀ = v := by
    intro v hv
    refine exists_add_eq_of_forall_bil₀_eq_zero hs2 fun v' hv' => ?_
    have hsum : v + v' ∈ co1Fix s := by
      show co1Act s (v + v') = v + v'
      rw [map_add, hv, hv']
    have e := CFSG.Sporadic.Co1.Module.q₀_add v v'
    rw [hB.2.2 _ hsum, hB.2.2 _ hv, hB.2.2 _ hv'] at e
    simpa using e.symm
  have hsinv : s⁻¹ = s := @inv_eq_of_mul_eq_one_right Co1 _ s s hs2
  have hφx : L.φ x⁻¹ = s := by rw [map_inv, ← hs, hsinv]
  have hstep : ∀ y ∈ Subgroup.centralizer ({s} : Set Co1), ∃ g : Subgroup.centralizer ({w} : Set G),
      L.φ g = y ∧ ((g : G) * x' * (g : G)⁻¹ = x' ∨ (g : G) * x' * (g : G)⁻¹ = x' * w) := by
    intro y hy
    obtain ⟨c, rfl⟩ := L.φ_surj y
    set qC : Subgroup.centralizer ({w} : Set G) := x⁻¹ * c * x * c⁻¹ with hqC
    have hqφ : L.φ qC = 1 := by
      have hyc : L.φ c * s = s * L.φ c := (Subgroup.mem_centralizer_singleton_iff (G := Co1)).mp hy
      rw [hqC, map_mul, map_mul, map_mul, map_inv, map_inv, ← hs]
      exact inv_mul_mul_mul_inv_eq_one hyc
    have hqQ : (qC : G) ∈ leechQ w := (L.φ_ker qC).1 hqφ
    have hxx : x' * x' = 1 := by
      have := pow_orderOf_eq_one x'
      rwa [hx2, pow_two] at this
    have hxinv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hxx
    have hq1 : x' * (qC : G) * x'⁻¹ = (qC : G)⁻¹ := by
      have e1 : (qC : G) = x'⁻¹ * (c : G) * x' * (c : G)⁻¹ := rfl
      have e2 : ((c : G) * x' * (c : G)⁻¹) * ((c : G) * x' * (c : G)⁻¹) = 1 := by
        calc _ = (c : G) * (x' * x') * (c : G)⁻¹ := by group
          _ = 1 := by rw [hxx]; group
      rw [e1, hxinv]
      rw [hxinv] at e1
      calc x' * (x' * ↑c * x' * (↑c)⁻¹) * x' = x' * x' * (↑c * x' * (↑c)⁻¹) * x' := by group
        _ = (↑c * x' * (↑c)⁻¹) * x' := by rw [hxx, one_mul]
        _ = (x' * ↑c * x' * (↑c)⁻¹)⁻¹ := by
          rw [← mul_eq_one_iff_eq_inv]
          calc ↑c * x' * (↑c)⁻¹ * x' * (x' * ↑c * x' * (↑c)⁻¹)
              = ↑c * x' * (↑c)⁻¹ * (x' * x') * ↑c * x' * (↑c)⁻¹ := by group
            _ = 1 := by rw [hxx, mul_one]; simpa only [mul_assoc] using e2
    have hvq : L.vec (qC : G) ∈ co1Fix s := by
      have h1 := L.vec_conj x (qC : G) hqQ
      rw [← hx', hq1, L.vec_inv hqQ] at h1
      exact h1.symm
    obtain ⟨w₀, hw₀⟩ := hfixadd _ hvq
    obtain ⟨p, hpQ, hpv⟩ := L.vec_surj w₀
    have hpC : p ∈ Subgroup.centralizer ({w} : Set G) := L.mem_centralizer hpQ
    set r : G := x'⁻¹ * p * x' * p⁻¹ with hr
    have hrQ : r ∈ leechQ w := by
      have h1 : x'⁻¹ * p * x'⁻¹⁻¹ ∈ leechQ w := L.conj_mem' (inv_mem hxw) hpQ
      rw [inv_inv] at h1
      exact mul_mem h1 (inv_mem hpQ)
    have hrv : L.vec r = L.vec (qC : G) := by
      have h1 : x'⁻¹ * p * x'⁻¹⁻¹ ∈ leechQ w := L.conj_mem' (inv_mem hxw) hpQ
      rw [hr, L.vec_mul _ (by rw [inv_inv] at h1; exact h1) _ (inv_mem hpQ), L.vec_inv hpQ]
      have h2 := L.vec_conj x⁻¹ p hpQ
      have e : ((x⁻¹ : Subgroup.centralizer ({w} : Set G)) : G) = x'⁻¹ := rfl
      rw [e, inv_inv, hφx, hpv] at h2
      rw [h2, hpv, ← hw₀]
    refine ⟨⟨p, hpC⟩⁻¹ * c, ?_, ?_⟩
    · rw [map_mul, map_inv, (L.φ_ker _).2 hpQ, inv_one, one_mul]
    · have hcx : (c : G) * x' * (c : G)⁻¹ = x' * (qC : G) := by
        show (c : G) * x' * (c : G)⁻¹ = x' * (x'⁻¹ * (c : G) * x' * (c : G)⁻¹)
        group
      have hg : ((⟨p, hpC⟩⁻¹ * c : Subgroup.centralizer ({w} : Set G)) : G) = p⁻¹ * (c : G) := rfl
      rw [hg]
      have hpw : p * w = w * p := Subgroup.mem_centralizer_singleton_iff.mp hpC
      rcases L.eq_or_eq_mul_z hrQ hqQ hrv with he | he
      · left
        calc p⁻¹ * ↑c * x' * (p⁻¹ * ↑c)⁻¹ = p⁻¹ * (↑c * x' * (↑c)⁻¹) * p := by group
          _ = p⁻¹ * (x' * r) * p := by rw [hcx, he]
          _ = x' := by rw [hr]; group
      · right
        have hww : w * w = 1 := L.z_mul_self
        calc p⁻¹ * ↑c * x' * (p⁻¹ * ↑c)⁻¹ = p⁻¹ * (↑c * x' * (↑c)⁻¹) * p := by group
          _ = p⁻¹ * (x' * (qC : G)) * p := by rw [hcx]
          _ = p⁻¹ * (x' * (r * w)) * p := by
            have hqr : (qC : G) = r * w := by rw [he, mul_assoc, hww, mul_one]
            rw [hqr]
          _ = x' * (p⁻¹ * w * p) := by rw [hr]; group
          _ = x' * w := by
            rw [mul_assoc p⁻¹, ← hpw]; group
  set D : Subgroup G := Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x'} : Set G)
    with hDdef
  have hHle : L.image D ≤ Subgroup.centralizer ({s} : Set Co1) := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := L.mem_image.1 hy
    rw [Subgroup.mem_centralizer_singleton_iff (G := Co1)]
    have hcx : c * x = x * c := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hc.2)
    rw [hs, ← map_mul, ← map_mul, hcx]
  have hww : w * w = 1 := L.z_mul_self
  have hwcent : ∀ g : Subgroup.centralizer ({w} : Set G), (g : G) * w = w * (g : G) :=
    fun g => Subgroup.mem_centralizer_singleton_iff.mp g.2
  have hindex : Nat.card ↥(Subgroup.centralizer ({s} : Set Co1)) ≤ 2 * Nat.card ↥(L.image D) := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    refine ncard_le_two_mul_of_coset (fun q _ hq => hq) ?_
    intro y₀ hy₀ y hy hy₀H hyH
    obtain ⟨g₀, hg₀φ, hg₀⟩ := hstep y₀ hy₀
    obtain ⟨g, hgφ, hg⟩ := hstep y hy
    have hmemD : ∀ k : Subgroup.centralizer ({w} : Set G), (k : G) * x' * (k : G)⁻¹ = x' →
        (k : G) ∈ D := fun k hk => ⟨k.2, Subgroup.mem_centralizer_singleton_iff.mpr (by
          calc (k : G) * x' = (k : G) * x' * (k : G)⁻¹ * (k : G) := by group
            _ = x' * (k : G) := by rw [hk])⟩
    have hg₀' : (g₀ : G) * x' * (g₀ : G)⁻¹ = x' * w := hg₀.resolve_left fun he =>
      hy₀H (L.mem_image.2 ⟨g₀, hmemD g₀ he, hg₀φ⟩)
    have hg' : (g : G) * x' * (g : G)⁻¹ = x' * w := hg.resolve_left fun he =>
      hyH (L.mem_image.2 ⟨g, hmemD g he, hgφ⟩)
    refine L.mem_image.2 ⟨g₀⁻¹ * g, hmemD _ ?_, by rw [map_mul, map_inv, hg₀φ, hgφ]⟩
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    have hg₀inv : (g₀ : G)⁻¹ * x' * (g₀ : G) = x' * w := by
      have e : x' = (g₀ : G)⁻¹ * x' * (g₀ : G) * w := by
        rw [← inv_mul_mul_mul_of_commute (hwcent g₀), ← hg₀']; group
      calc (g₀ : G)⁻¹ * x' * (g₀ : G) = (g₀ : G)⁻¹ * x' * (g₀ : G) * w * w⁻¹ := by group
        _ = x' * w := by rw [← e, hwinv]
    show (g₀⁻¹ * g : Subgroup.centralizer ({w} : Set G)) * x' *
      ((g₀⁻¹ * g : Subgroup.centralizer ({w} : Set G)) : G)⁻¹ = x'
    have e1 : ((g₀⁻¹ * g : Subgroup.centralizer ({w} : Set G)) : G) = (g₀ : G)⁻¹ * (g : G) := rfl
    rw [e1]
    calc (g₀ : G)⁻¹ * (g : G) * x' * ((g₀ : G)⁻¹ * (g : G))⁻¹
        = (g₀ : G)⁻¹ * ((g : G) * x' * (g : G)⁻¹) * (g₀ : G) := by group
      _ = (g₀ : G)⁻¹ * x' * (g₀ : G) * w := by
          rw [hg', inv_mul_mul_mul_of_commute (hwcent g₀)]
      _ = x' := by rw [hg₀inv, mul_assoc, hww, mul_one]
  set K : Subgroup G := leechQ x' ⊓ Subgroup.centralizer ({w} : Set G) with hKdef
  have hKD : K ≤ D := fun q hq => ⟨hq.2, Lx.mem_centralizer hq.1⟩
  have hNH : L.image K ≤ L.image D := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := L.mem_image.1 hy
    exact L.mem_image.2 ⟨c, hKD hc, rfl⟩
  have hnorm : ∀ y ∈ L.image D, ∀ n ∈ L.image K, y * n * y⁻¹ ∈ L.image K := by
    intro y hy n hn
    obtain ⟨c, hc, rfl⟩ := L.mem_image.1 hy
    obtain ⟨d, hd, rfl⟩ := L.mem_image.1 hn
    refine L.mem_image.2 ⟨c * d * c⁻¹, ⟨?_, (c * d * c⁻¹).2⟩, by rw [map_mul, map_mul, map_inv]⟩
    exact Lx.conj_mem' hc.2 hd.1
  have hpK : IsPGroup 2 ↥K :=
    (IsPGroup.of_card (hG.2.of_isConj hxB).card_leechQ).to_le inf_le_left
  have hpN : IsPGroup 2 ↥(L.image K) := by
    have h1 : IsPGroup 2 ↥(K.subgroupOf (Subgroup.centralizer ({w} : Set G))) :=
      hpK.comap_of_injective _ (Subgroup.subtype_injective _)
    have himg : L.image K = (K.subgroupOf (Subgroup.centralizer ({w} : Set G))).map L.φ := by
      ext y
      rw [L.mem_image, Subgroup.mem_map]
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact ⟨c, Subgroup.mem_subgroupOf.2 hc, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨c, Subgroup.mem_subgroupOf.1 hc, rfl⟩
    rw [himg]
    exact h1.map L.φ
  have hN := hO2 (L.image D) hHle hindex (L.image K) hNH hnorm hpN
  have hKcard := L.card_eq_card_image_mul K inf_le_right
  obtain ⟨u, huU, hu1⟩ : ∃ u ∈ leechQ w ⊓ K, u ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : leechQ w ⊓ K = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hne
    rw [hbot, Subgroup.card_bot, mul_one] at hKcard
    omega
  obtain ⟨huQw, huQx, huCw⟩ : u ∈ leechQ w ∧ u ∈ leechQ x' ∧
      u ∈ Subgroup.centralizer ({w} : Set G) := ⟨huU.1, huU.2.1, huU.2.2⟩
  have huw : u ≠ w := fun he => hwQx (he ▸ huQx)
  have hux : u ≠ x' := fun he => hxQ (he ▸ huQw)
  have huCx : u ∈ Subgroup.centralizer ({x'} : Set G) := Lx.mem_centralizer huQx
  have hvu0 : L.vec u ≠ 0 := fun h0 => by
    rcases (L.vec_eq_zero u huQw).1 h0 with h1 | h1
    · exact hu1 h1
    · exact huw h1
  have hvuF : L.vec u ∈ co1Fix s := hvecW u huQw huCx
  have hvu4 : L.vec u ∈ co1Orbit 2 := htype _ hvuF hvu0
  have huu : u * u = 1 := (L.mul_self_eq_one_iff huQw).2 (hB.2.2 _ hvuF)
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
  have hstab4 : Nat.card ↥(co1Stab (L.vec u)) = 501397585920 := by
    have h1 := card_co1Stab_mul_ncard_co1Orbit hvu4
    rw [ncard_co1Orbit_two, CFSG.Sporadic.Co1.card_Co1] at h1
    omega
  have huA : ¬ IsConj a u := fun hA => by
    have h1 := card_centralizer_inf_of_mem_leechQ_two hSLS hTV hL hG hw huQw hA
    have h2 := L.card_eq_card_image_mul
      (Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({u} : Set G)) inf_le_left
    have h3 : L.image (Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({u} : Set G))
        ≤ co1Stab (L.vec u) := by
      intro y hy
      obtain ⟨c, hc, rfl⟩ := L.mem_image.1 hy
      show co1Act (L.φ c) (L.vec u) = L.vec u
      rw [← L.vec_conj c u huQw]
      congr 1
      have hcu : (c : G) * u = u * (c : G) := Subgroup.mem_centralizer_singleton_iff.mp hc.2
      rw [hcu]; group
    have h4 := Subgroup.card_le_of_le h3
    have h5 : Nat.card ↥(leechQ w ⊓ (Subgroup.centralizer ({w} : Set G) ⊓
        Subgroup.centralizer ({u} : Set G))) ≤ 2 ^ 25 := by
      rw [← (hG.2.of_isConj hw).card_leechQ]
      exact Subgroup.card_le_of_le inf_le_left
    rw [h1, hstab4] at *
    have h6 := Nat.mul_le_mul h4 h5
    rw [← h2] at h6
    norm_num [tableVOrderZ] at h6
  have huB : IsConj z₀ u := by
    rcases orderOf_eq_two_mem_leechQ hSLS hTV hL hG hw huQw hu2 with h1 | h1 | h1
    · exact absurd h1 huw
    · exact absurd h1 huA
    · exact h1
  have hcwu := card_centralizer_inf_of_mem_leechQ_four hSLS hTV hL hG hw huQw huw huB
  have hcxu := card_centralizer_inf_of_mem_leechQ_four hSLS hTV hL hG hxB huQx hux huB
  have hcu := h.card_centralizer huB
  set E : Subgroup G := D ⊓ Subgroup.centralizer ({u} : Set G) with hEdef
  have hE : Nat.card E ≤ 2 ^ 13 * 491520 := by
    have h1 := L.card_eq_card_image_mul E (inf_le_left.trans inf_le_left)
    have h2 : Nat.card ↥(leechQ w ⊓ E) ≤ 2 ^ 13 :=
      (Subgroup.card_le_of_le (inf_le_inf_left _ (inf_le_left.trans inf_le_right))).trans hW
    have h3 : L.image E ≤ Subgroup.centralizer ({s} : Set Co1) ⊓ co1Stab (L.vec u) := by
      intro y hy
      refine ⟨hHle ((fun y hy => ?_ : L.image E ≤ L.image D) y hy), ?_⟩
      · obtain ⟨c, hc, rfl⟩ := L.mem_image.1 hy
        exact L.mem_image.2 ⟨c, hc.1, rfl⟩
      · obtain ⟨c, hc, rfl⟩ := L.mem_image.1 hy
        show co1Act (L.φ c) (L.vec u) = L.vec u
        rw [← L.vec_conj c u huQw]
        congr 1
        have hcu : (c : G) * u = u * (c : G) := Subgroup.mem_centralizer_singleton_iff.mp hc.2
        rw [hcu]; group
    have h4 := Subgroup.card_le_of_le h3
    have h5 := ncard_mul_card_le_of_forall_exists (fun g v => co1Act g v)
      (fun g h v => by simp only [map_mul, Module.End.mul_apply])
      (K := Subgroup.centralizer ({s} : Set Co1))
      (S := Subgroup.centralizer ({s} : Set Co1) ⊓ co1Stab (L.vec u)) inf_le_left
      (v := L.vec u) (fun t ht => ht.2) (F := co1Fix s \ {0}) (fun v hv =>
        htrans (L.vec u) hvuF v hv.1 hvu0 hv.2)
    have h6 : (co1Fix s \ {0}).ncard = 4095 := by
      rw [Set.ncard_sdiff_singleton_of_mem (show (0 : Fin 24 → ZMod 2) ∈ co1Fix s from
        map_zero (co1Act s)), hB.2.1]
      norm_num
    rw [h6] at h5
    rw [h1]
    calc Nat.card ↥(L.image E) * Nat.card ↥(leechQ w ⊓ E) ≤ 491520 * 2 ^ 13 := by
          refine Nat.mul_le_mul ?_ h2
          omega
      _ = 2 ^ 13 * 491520 := by ring
  have hr := Subgroup.relIndex_inf_le (H := Subgroup.centralizer ({w} : Set G))
    (K := Subgroup.centralizer ({x'} : Set G)) (L := Subgroup.centralizer ({u} : Set G))
  have e1 := Subgroup.relIndex_mul_card (H := D) (K := Subgroup.centralizer ({u} : Set G))
  have e2 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({w} : Set G))
    (K := Subgroup.centralizer ({u} : Set G))
  have e3 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({x'} : Set G))
    (K := Subgroup.centralizer ({u} : Set G))
  rw [hcwu] at e2
  rw [hcxu] at e3
  set m : ℕ := 2 ^ 45 * 3 ^ 3 * 5 * 7 * 11 * 23 with hm
  set l : ℕ := Nat.card ↥(Subgroup.centralizer ({u} : Set G)) with hl
  have hlpos : 0 < l := Nat.card_pos
  have hkey : l * (m * m) ≤ l * (l * Nat.card E) := by
    calc l * (m * m) = (D.relIndex (Subgroup.centralizer ({u} : Set G)) * Nat.card E) * (m * m) :=
          by rw [← e1]
      _ ≤ ((Subgroup.centralizer ({w} : Set G)).relIndex (Subgroup.centralizer ({u} : Set G)) *
            (Subgroup.centralizer ({x'} : Set G)).relIndex (Subgroup.centralizer ({u} : Set G))) *
            Nat.card E * (m * m) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hr)
      _ = ((Subgroup.centralizer ({w} : Set G)).relIndex (Subgroup.centralizer ({u} : Set G)) * m) *
            ((Subgroup.centralizer ({x'} : Set G)).relIndex (Subgroup.centralizer ({u} : Set G)) *
              m) * Nat.card E := by ring
      _ = l * (l * Nat.card E) := by rw [e2, e3]; ring
  have h1 := Nat.le_of_mul_le_mul_left hkey hlpos
  have h2 : m * m ≤ l * (2 ^ 13 * 491520) := h1.trans (Nat.mul_le_mul_left _ hE)
  rw [hcu, hm] at h2
  norm_num at h2


theorem s31_six'
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hLI : LeechInvolutionStatement) (h13 : Co1ModuleUniqueness)
    (hI : Co1InvolutionFacts) (h2B : Co1TwoBFacts) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {w : G}
    (hw : IsConj z₀ w) (φ : Subgroup.centralizer ({w} : Set G) →* Co1)
    (hφs : Function.Surjective φ)
    (hφk : φ.ker = CFSG.pCore 2 (Subgroup.centralizer ({w} : Set G)))
    (x : Subgroup.centralizer ({w} : Set G)) (hx : orderOf x = 2) : ¬ IsCo1TwoB (φ x) := by
  obtain ⟨L, rfl⟩ := exists_leechSystem_of_hom h13 (hG.2.of_isConj hw) φ hφs hφk
  exact s31_six hSLS hTV hL hLI h13 hI h2B hG hw L x hx

theorem s31_seven
    {G' : Type} [Group G'] [Finite G] [Finite G'] {d₀' : B}
    (hSLS : SLSStatement d₀) (hSLS' : SLSStatement d₀')
    (hTV : TableVIn G) (hTV' : TableVIn G') (hL : LeechStatement) (hLI : LeechInvolutionStatement)
    (h13 : Co1ModuleUniqueness) (hI : Co1InvolutionFacts) (h2B : Co1TwoBFacts)
    (hLT : LeechTypeUniqueness) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {a' z₀' : G'}
    (hG' : GMSF1Type d₀' a' z₀') :
    Nonempty (Subgroup.centralizer ({z₀} : Set G) ≃* Subgroup.centralizer ({z₀'} : Set G')) := by
  obtain ⟨φ, hφs, hφk⟩ := hG.2.2.2.2.1
  obtain ⟨φ', hφs', hφk'⟩ := hG'.2.2.2.2.1
  exact hLT G G' z₀ z₀' hG.2 hG'.2 φ φ' hφs hφk hφs' hφk'
    (s31_six' hSLS hTV hL hLI h13 hI h2B hG (IsConj.refl z₀) φ hφs hφk)
    (s31_six' hSLS' hTV' hL hLI h13 hI h2B hG' (IsConj.refl z₀') φ' hφs' hφk')

end CFSG.Monster.GMS
