module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerLeafDefs
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerToralAlg
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerToralAut
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofKG
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofOut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality

namespace D4Inner

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem conj_mul_pow_three {G : Type*} [Group G] (g : G) (β : MulAut G) :
    (MulAut.conj g * β) ^ 3 = MulAut.conj (g * β g * β (β g)) * β ^ 3 := by
  ext x
  rw [pow_three, pow_three]
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem mulAut_mul_conj' {G : Type*} [Group G] (ψ : MulAut G) (y : G) :
    ψ * MulAut.conj y = MulAut.conj (ψ y) * ψ := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem conj_mem_commutator_self {G : Type*} [Group G] {H : Subgroup G} {c : G} (hc : c ∈ H)
    {y : G} (hy : y ∈ ⁅H, H⁆) : c * y * c⁻¹ ∈ ⁅H, H⁆ := by
  have hH : H.map (MulAut.conj c).toMonoidHom = H := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact H.mul_mem (H.mul_mem hc hw) (H.inv_mem hc)
    · intro hz
      refine ⟨c⁻¹ * z * c, H.mul_mem (H.mul_mem (H.inv_mem hc) hz) hc, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have h := Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hy
  rw [Subgroup.map_commutator, hH] at h
  simpa [MulAut.conj_apply] using h

theorem exists_mul_eq_of_norm_eq_one {G : Type*} [Group G] {V D P : Subgroup G} [Finite V]
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV3 : ∀ v ∈ V, v ^ 3 = 1)
    (hV81 : Nat.card V = 3 ^ 4) (α : MulAut G) (hαV : ∀ v ∈ V, α v ∈ V)
    (hVD : Nat.card ↥(V ⊓ D) = 3 ^ 2) (hVP : Nat.card ↥(V ⊓ P) = 3 ^ 2)
    (hVDP : Nat.card ↥(V ⊓ D ⊓ P) = 3) (hαD : ∀ d ∈ D, α d = d)
    (hfix : ∀ E : Subgroup G, E ≤ V → (∀ e ∈ E, α e = e) → Nat.card E ≤ 3 ^ 2)
    (hδ : ∀ v ∈ V, α v * v⁻¹ ∈ P) (hPN : ∀ c ∈ V ⊓ P, c * α c * α (α c) = 1)
    {u : G} (huV : u ∈ V) (hu : u * α u * α (α u) = 1) :
    ∃ d ∈ V ⊓ D, ∃ c ∈ V ⊓ P, d * c = u := by
  letI : CommGroup V := { (inferInstance : Group V) with
    mul_comm := fun x y => Subtype.ext (hcomm x x.2 y y.2) }
  let σ : V →* V :=
    MonoidHom.mk' (fun v => ⟨α v, hαV v v.2⟩) (fun a b => Subtype.ext (map_mul α (a : G) b))
  have hσ : ∀ v : V, (σ v : G) = α v := fun v => rfl
  have hcardOf : ∀ H : Subgroup G, Nat.card ↥(H.subgroupOf V) = Nat.card ↥(V ⊓ H) := fun H => by
    rw [← Subgroup.card_map_of_injective V.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have hDP : Nat.card ↥(D.subgroupOf V ⊓ P.subgroupOf V) = 3 := by
    rw [← Subgroup.card_map_of_injective V.subtype_injective,
      Subgroup.map_inf_eq _ _ _ V.subtype_injective, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype]
    have h : D ⊓ V ⊓ (P ⊓ V) = V ⊓ D ⊓ P := by
      ext x; simp only [Subgroup.mem_inf]; tauto
    rw [h, hVDP]
  have hfix' : ∀ E : Subgroup V, (∀ e ∈ E, σ e = e) → Nat.card E ≤ 3 ^ 2 := by
    intro E hE
    rw [← Subgroup.card_map_of_injective V.subtype_injective]
    refine hfix _ (by rintro _ ⟨x, -, rfl⟩; exact x.2) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (hE x hx)
  have hmem := mem_sup_of_norm_eq_one (A := V) (fun a => Subtype.ext (hV3 a a.2)) hV81 σ
    (by rw [hcardOf]; exact hVD) (by rw [hcardOf]; exact hVP) hDP
    (fun d hd => Subtype.ext (hαD d (Subgroup.mem_subgroupOf.1 hd))) hfix'
    (fun a => by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hσ]
      exact hδ a a.2)
    (fun c hc => Subtype.ext (by
      simpa [hσ] using hPN c ⟨c.2, Subgroup.mem_subgroupOf.1 hc⟩))
    (u := ⟨u, huV⟩) (Subtype.ext (by simpa [hσ] using hu))
  obtain ⟨d, hd, c, hc, hdc⟩ := Subgroup.mem_sup.1 hmem
  exact ⟨d, ⟨d.2, Subgroup.mem_subgroupOf.1 hd⟩, c, ⟨c.2, Subgroup.mem_subgroupOf.1 hc⟩,
    congrArg Subtype.val hdc⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem mem_centralizer_of_fix {φ : MulAut (Om8 K)} {D : Subgroup (Om8 K)}
    (hφ : ∀ d ∈ D, φ d = d) {t : Om8 K} (ht : t ∈ Subgroup.centralizer (D : Set (Om8 K))) :
    φ t ∈ Subgroup.centralizer (D : Set (Om8 K)) := by
  rw [Subgroup.mem_centralizer_iff] at ht ⊢
  intro d hd
  rw [← hφ d hd, ← map_mul, ← map_mul, ht d hd]

theorem norm_mul_of_comm {G : Type*} [Group G] {T : Subgroup G}
    (hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (φ : MulAut G) (hφT : ∀ t ∈ T, φ t ∈ T)
    {a b : G} (ha : a ∈ T) (hb : b ∈ T) :
    a * b * φ (a * b) * φ (φ (a * b)) = a * φ a * φ (φ a) * (b * φ b * φ (φ b)) := by
  haveI : IsMulCommutative T := ⟨⟨fun x y => Subtype.ext (hTab x x.2 y y.2)⟩⟩
  have key : ((⟨a, ha⟩ : T) * ⟨b, hb⟩) * (⟨φ a, hφT a ha⟩ * ⟨φ b, hφT b hb⟩) *
      (⟨φ (φ a), hφT _ (hφT a ha)⟩ * ⟨φ (φ b), hφT _ (hφT b hb)⟩) =
      ((⟨a, ha⟩ : T) * ⟨φ a, hφT a ha⟩ * ⟨φ (φ a), hφT _ (hφT a ha)⟩) *
      (⟨b, hb⟩ * ⟨φ b, hφT b hb⟩ * ⟨φ (φ b), hφT _ (hφT b hb)⟩) := by
    ac_rfl
  have key' := congrArg Subtype.val key
  simp only [Subgroup.coe_mul] at key'
  simp only [map_mul]
  exact key'

theorem pow_apply_of_fix {G : Type*} [Group G] {J : Subgroup G} {γ : MulAut G}
    (hγ : ∀ y ∈ J, γ y = y) (m : ℕ) : ∀ y ∈ J, (γ ^ m) y = y := by
  induction m with
  | zero => intro y _; rfl
  | succ m ih => intro y hy; rw [pow_succ, MulAut.mul_apply, hγ y hy, ih y hy]

theorem toralOn_false_of_leaves
    (hD0 : ∀ {s : Om8 K} {J : Subgroup (Om8 K)}, s ^ 3 = 1 → D4Rank.omFixDim s = 2 →
      IsComponentOf J (ggAutFixedSubgroup (MulAut.conj s)) → J = centDer s)
    (hKSF : ∀ {s : Om8 K}, s ^ 3 = 1 → D4Rank.omFixDim s = 2 →
      ∃ γ : MulAut (Om8 K), D4Bstar.IsTriPart 1 γ ∧ γ ^ 3 = 1 ∧ (∀ y ∈ centDer s, γ y = y) ∧
        ∀ p ∈ Subgroup.centralizer (centDer s : Set (Om8 K)), p * γ p * γ (γ p) = 1)
    (hD5 : ∀ {s : Om8 K} {φ : MulAut (Om8 K)}, s ^ 3 = 1 → D4Rank.omFixDim s = 2 →
      φ ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range → (∀ y ∈ centDer s, φ y = y) →
        φ ∈ Inn (Om8 K))
    {A : Subgroup (MulAut (Om8 K))} {s : Om8 K} {J : Subgroup (Om8 K)}
    (hloc : GGKLocal A (MulAut.conj s) J) (hA : Nat.card A = 3 ^ 3)
    (hd : D4Rank.omFixDim s = 2)
    (hdat : ∀ a ∈ A, a ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range → a ∈ Inn (Om8 K))
    (hout : ∃ a ∈ A, a ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)
    (htor : ToralOn A s J) : False := by
  classical
  obtain ⟨⟨hAe, hσA, hσ1, hJc, hAJ⟩, hker⟩ := hloc
  obtain ⟨D, V, hDJ, hTab, hV, hV81, hVD, hVP, hVDP, hreal⟩ := htor
  obtain ⟨α, hαA, hα⟩ := hout
  set T := Subgroup.centralizer (D : Set (Om8 K)) with hT
  set CJ := Subgroup.centralizer (J : Set (Om8 K)) with hCJ
  have hα3 : α ^ 3 = 1 := hAe.2 α hαA
  have hs3 : s ^ 3 = 1 := NbrGraphD4.conj_injective (by rw [map_pow, hAe.2 _ hσA, map_one])
  have hs1 : s ≠ 1 := fun h => hσ1 (by rw [h, map_one])
  have hJ : J = centDer s := hD0 hs3 hd hJc
  have hsVDP : s ∈ V ⊓ D ⊓ CJ := by rw [hVDP]; exact Subgroup.mem_zpowers s
  have hsD : s ∈ D := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hsVDP).1).2
  have hCJT : CJ ≤ T := Subgroup.centralizer_le hDJ
  have hTs : ∀ t ∈ T, t ∈ Subgroup.centralizer ({s} : Set (Om8 K)) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 ht s hsD)).symm
  have hTnorm : ∀ t ∈ T, ∀ j ∈ J, t * j * t⁻¹ ∈ J := fun t ht j hj => by
    rw [hJ] at hj ⊢; exact conj_mem_commutator_self (hTs t ht) hj
  have hcommT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := hTab
  have hVT : ∀ v ∈ V, v ∈ T := fun v hv => ((hV v).1 hv).1
  have hV3 : ∀ v ∈ V, v ^ 3 = 1 := fun v hv => ((hV v).1 hv).2
  obtain ⟨u, huV, hu⟩ := hreal α hαA
  have huT := hVT u huV
  have hαD : ∀ d ∈ D, α d = d := fun d hd => by
    rw [hu d (hDJ hd), (Subgroup.mem_centralizer_iff.1 huT d hd).symm, mul_inv_cancel_right]
  have hαT : ∀ t ∈ T, α t ∈ T := fun t ht => mem_centralizer_of_fix hαD ht
  obtain ⟨γ, hγ1, hγ3, hγfix, hγN⟩ := hKSF hs3 hd
  rw [← hJ] at hγfix hγN
  have hγD : ∀ d ∈ D, γ d = d := fun d hd => hγfix d (hDJ hd)
  have hγT : ∀ t ∈ T, γ t ∈ T := fun t ht => mem_centralizer_of_fix hγD ht
  have hγCJ : ∀ c ∈ CJ, γ c ∈ CJ := fun c hc => mem_centralizer_of_fix hγfix hc
  obtain ⟨k, hk, hkα⟩ := exists_isTriPart_of_not_mem hα3 hα
  have hk3 : k ≤ 3 := by omega
  set β := MulAut.conj u⁻¹ * α with hβ
  have hβfix : ∀ j ∈ J, β j = j := fun j hj => by
    rw [hβ, MulAut.mul_apply, hu j hj, MulAut.conj_apply]; group
  have hβk : D4Bstar.IsTriPart k β := by
    have h0 : D4Bstar.IsTriPart 0 (MulAut.conj u⁻¹) :=
      ⟨u⁻¹, 1, by rw [pow_zero, map_one, mul_one, mul_one]⟩
    have h := h0.mul hkα
    rwa [zero_add] at h
  set φ := β * γ ^ (3 - k) with hφ
  have hφ0 : D4Bstar.IsTriPart 0 φ := by
    have h := (hβk.mul (hγ1.pow (3 - k))).mod_three
    rwa [show (k + (3 - k) * 1) % 3 = 0 by omega] at h
  have hφfix : ∀ y ∈ centDer s, φ y = y := fun y hy => by
    rw [← hJ] at hy
    rw [hφ, MulAut.mul_apply, pow_apply_of_fix hγfix _ y hy, hβfix y hy]
  obtain ⟨p, hp⟩ := hD5 hs3 hd (isTriPart_zero_iff_mem_sup.1 hφ0) hφfix
  have hpCJ : p ∈ CJ := Subgroup.mem_centralizer_iff.2 fun j hj => by
    have h := DFunLike.congr_fun hp j
    rw [MulAut.conj_apply, hφfix j (hJ ▸ hj)] at h
    nth_rewrite 1 [← h]; group
  have hpT := hCJT hpCJ
  have hγk : γ ^ (3 - k) * γ ^ k = 1 := by rw [← pow_add, Nat.sub_add_cancel hk3, hγ3]
  have hαeq : α = MulAut.conj (u * p) * γ ^ k := by
    have h1 : MulAut.conj u⁻¹ * α * γ ^ (3 - k) = MulAut.conj p := hp.symm
    calc α = MulAut.conj u * (MulAut.conj u⁻¹ * α * γ ^ (3 - k)) * γ ^ k := by
          rw [mul_assoc, mul_assoc, hγk, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel,
            map_one, one_mul]
      _ = MulAut.conj (u * p) * γ ^ k := by rw [h1, ← map_mul]
  have powT : ∀ m : ℕ, ∀ t ∈ T, (γ ^ m) t ∈ T := fun m => by
    induction m with
    | zero => intro t ht; simpa using ht
    | succ m ih => intro t ht; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hγT t ht)
  have hγk3 : (γ ^ k) ^ 3 = 1 := by
    rw [← pow_mul, show k * 3 = 3 * k from Nat.mul_comm k 3, pow_mul, hγ3, one_pow]
  have hNup : u * p * (γ ^ k) (u * p) * (γ ^ k) ((γ ^ k) (u * p)) = 1 := by
    have h := conj_mul_pow_three (u * p) (γ ^ k)
    rw [← hαeq, hα3, hγk3, mul_one] at h
    exact NbrGraphD4.conj_injective (h.symm.trans (map_one _).symm)
  have hNCJ : ∀ c ∈ CJ, c * (γ ^ k) c * (γ ^ k) ((γ ^ k) c) = 1 := fun c hc => by
    rcases hk with rfl | rfl
    · simpa [pow_one] using hγN c hc
    · have hcT := hCJT hc
      have h4 : (γ ^ 2) ((γ ^ 2) c) = γ c := by
        rw [← MulAut.mul_apply, ← pow_add, show (2 : ℕ) + 2 = 3 + 1 by norm_num, pow_add, hγ3,
          one_mul, pow_one]
      have h2 : (γ ^ 2) c = γ (γ c) := by rw [pow_two, MulAut.mul_apply]
      rw [h4, h2, mul_assoc, hcommT _ (hγT _ (hγT _ hcT)) _ (hγT _ hcT), ← mul_assoc]
      exact hγN c hc
  have hNu : u * (γ ^ k) u * (γ ^ k) ((γ ^ k) u) = 1 := by
    have h := norm_mul_of_comm hcommT (γ ^ k) (powT k) huT hpT
    rw [hNup, hNCJ p hpCJ, mul_one] at h
    exact h.symm
  have hαγ : ∀ t ∈ T, α t = (γ ^ k) t := fun t ht => by
    rw [hαeq, MulAut.mul_apply, MulAut.conj_apply,
      hcommT _ (T.mul_mem huT hpT) _ (powT k t ht), mul_inv_cancel_right]
  have hαconj : ∀ a ∈ T, ∀ j ∈ J, α a * j * (α a)⁻¹ = a * j * a⁻¹ := fun a ha j hj => by
    have hj'J : u⁻¹ * j * u ∈ J := by simpa using hTnorm u⁻¹ (T.inv_mem huT) j hj
    have hαj' : α (u⁻¹ * j * u) = j := by rw [hu _ hj'J]; group
    have hc : Commute u a := hcommT u huT a ha
    have h1 : α (a * (u⁻¹ * j * u) * a⁻¹) = a * j * a⁻¹ := by
      rw [hu _ (hTnorm a ha _ hj'J)]
      calc u * (a * (u⁻¹ * j * u) * a⁻¹) * u⁻¹
          = (u * a * u⁻¹) * j * (u * a⁻¹ * u⁻¹) := by group
        _ = a * j * a⁻¹ := by
          rw [hc.eq, mul_inv_cancel_right, hc.inv_right.eq, mul_inv_cancel_right]
    rw [← h1, map_mul, map_mul, map_inv, hαj']
  have hαV : ∀ v ∈ V, α v ∈ V := fun v hv =>
    (hV _).2 ⟨hαT v (hVT v hv), by rw [← map_pow, hV3 v hv, map_one]⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfixV : ∀ E : Subgroup (Om8 K), E ≤ V → (∀ e ∈ E, α e = e) → Nat.card E ≤ 3 ^ 2 :=
    fun E hEV hEfix => NbrGraphD4.card_le_nine_of_not_mem hα3 hα
      ⟨⟨⟨fun x y => Subtype.ext (hcommT _ (hVT _ (hEV x.2)) _ (hVT _ (hEV y.2)))⟩⟩,
        fun g hg => hV3 g (hEV hg)⟩ hEfix
  have hδ : ∀ v ∈ V, α v * v⁻¹ ∈ CJ := fun v hv => by
    have hvT := hVT v hv
    refine Subgroup.mem_centralizer_iff.2 fun j hj => ?_
    have hc : α v * v⁻¹ = v⁻¹ * α v := hcommT _ (hαT v hvT) _ (T.inv_mem hvT)
    have h := hαconj v hvT j hj
    rw [hc]
    have h' : v⁻¹ * α v * j = v⁻¹ * (α v * j * (α v)⁻¹) * α v := by group
    rw [h', h]; group
  have hPN : ∀ c ∈ V ⊓ CJ, c * α c * α (α c) = 1 := fun c hc => by
    have hcT := hVT c (Subgroup.mem_inf.1 hc).1
    rw [hαγ (α c) (hαT c hcT), hαγ c hcT]
    exact hNCJ c (Subgroup.mem_inf.1 hc).2
  have hNuα : u * α u * α (α u) = 1 := by
    rw [hαγ (α u) (hαT u huT), hαγ u huT]
    exact hNu
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_norm_eq_one
    (fun x hx y hy => hcommT x (hVT x hx) y (hVT y hy)) hV3 hV81 α hαV hVD hVP
    (by rw [hVDP, Nat.card_zpowers, orderOf_eq_prime hs3 hs1]) hαD hfixV hδ hPN huV hNuα
  have hFeq : V ⊓ D = V ⊓ α.toMonoidHom.eqLocus (MonoidHom.id (Om8 K)) := by
    refine Subgroup.eq_of_le_of_card_ge
      (le_inf inf_le_left fun x hx => hαD x (Subgroup.mem_inf.1 hx).2) ?_
    rw [hVD]
    exact hfixV _ inf_le_left fun e he => (Subgroup.mem_inf.1 he).2
  set E₀ := A.comap (MulAut.conj : Om8 K →* MulAut (Om8 K)) with hE₀
  have hE₀le : E₀ ≤ V ⊓ D := by
    intro e he
    have he' : MulAut.conj e ∈ A := he
    obtain ⟨ue, hueV, hue⟩ := hreal _ he'
    have hueT := hVT ue hueV
    have hCe : ue⁻¹ * e ∈ CJ := Subgroup.mem_centralizer_iff.2 fun j hj => by
      have h := hue j hj
      rw [MulAut.conj_apply] at h
      calc j * (ue⁻¹ * e) = ue⁻¹ * (ue * j * ue⁻¹) * e := by group
        _ = ue⁻¹ * (e * j * e⁻¹) * e := by rw [h]
        _ = ue⁻¹ * e * j := by group
    have heT : e ∈ T := by
      have h := T.mul_mem hueT (hCJT hCe)
      rwa [mul_inv_cancel_left] at h
    have he3 : e ^ 3 = 1 := NbrGraphD4.conj_injective (by rw [map_pow, hAe.2 _ he', map_one])
    have heV : e ∈ V := (hV e).2 ⟨heT, he3⟩
    have hαe : α e = e := by
      have h1 : α * MulAut.conj e = MulAut.conj e * α :=
        congrArg Subtype.val (hAe.1.is_comm.comm ⟨α, hαA⟩ ⟨MulAut.conj e, he'⟩)
      rw [mulAut_mul_conj'] at h1
      exact NbrGraphD4.conj_injective (mul_right_cancel h1)
    rw [hFeq]
    exact ⟨heV, hαe⟩
  have hE₀map : E₀.map (MulAut.conj : Om8 K →* MulAut (Om8 K)) = A ⊓ Inn (Om8 K) := by
    ext a
    constructor
    · rintro ⟨γ, hγ, rfl⟩; exact ⟨hγ, γ, rfl⟩
    · rintro ⟨haA, γ, rfl⟩; exact ⟨γ, haA, rfl⟩
  have hE₀eq : E₀ = V ⊓ D := by
    refine Subgroup.eq_of_le_of_card_ge hE₀le ?_
    rw [hVD, ← Subgroup.card_map_of_injective NbrGraphD4.conj_injective, hE₀map]
    exact nine_le_card_inf_inner hAe hA hdat hαA hα
  have hyA : MulAut.conj y ∈ A := by
    have h : y ∈ E₀ := hE₀eq ▸ hy
    exact h
  have hyJ : y ∈ J := hDJ (Subgroup.mem_inf.1 hy).2
  have hzCJ : z ∈ CJ := (Subgroup.mem_inf.1 hz).2
  have hfixJ : ∀ j ∈ J, (α * (MulAut.conj y)⁻¹) j = j := fun j hj => by
    have hj' : y⁻¹ * j * y ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hyJ) hj) hyJ
    rw [MulAut.mul_apply, ← map_inv, MulAut.conj_apply, inv_inv, hu _ hj', ← hyz]
    have hzc : z * (y⁻¹ * j * y) = y⁻¹ * j * y * z :=
      ((Subgroup.mem_centralizer_iff.1 hzCJ) _ hj').symm
    calc y * z * (y⁻¹ * j * y) * (y * z)⁻¹ = y * (z * (y⁻¹ * j * y)) * z⁻¹ * y⁻¹ := by group
      _ = j := by rw [hzc]; group
  have hinn : α * (MulAut.conj y)⁻¹ ∈ Inn (Om8 K) :=
    (Subgroup.zpowers_le (H := Inn (Om8 K))).2 ⟨s, rfl⟩
      (hker _ (A.mul_mem hαA (A.inv_mem hyA)) hfixJ)
  apply hα
  have h : α = α * (MulAut.conj y)⁻¹ * MulAut.conj y := by group
  rw [h]
  exact Subgroup.mem_sup_left ((Inn (Om8 K)).mul_mem hinn ⟨y, rfl⟩)

end D4Inner

end CFSG.StandardType

end
