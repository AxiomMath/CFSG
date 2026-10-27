module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67Q8
public import CFSG.Quasithin.H13.VolIF956

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem isExtraspecial_of_mulEquiv_aux {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.IsExtraspecial 2 A) : CFSG.IsExtraspecial 2 B where
  center_order_p := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact h.center_order_p
  quotient_elementary_abelian :=
    CFSG.IsElementaryAbelian.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
        (Subgroup.map_center_eq e)) h.quotient_elementary_abelian
  quotient_nontrivial := by
    have := h.quotient_nontrivial
    exact (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
      (Subgroup.map_center_eq e)).symm.surjective.nontrivial

theorem isExtraspecialPlus2_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {n : ℕ}
    (hA : IsExtraspecialPlus2 A n) : IsExtraspecialPlus2 B n := by
  obtain ⟨hE, hcard, E, hrank⟩ := hA
  refine ⟨isExtraspecial_of_mulEquiv_aux e hE, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]
    exact hcard
  · refine ⟨E.map (e : A →* B), ?_⟩
    obtain ⟨f⟩ := hrank
    exact ⟨(Subgroup.equivMapOfInjective E (e : A →* B) e.injective).symm.trans f⟩

namespace Cfg1667

variable {M V W₁ W₂ : Subgroup G} {g : G}

theorem K_inf_centralizer_U_le (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    ((V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M)) ⊓
        centralizer ((V ⊓ conjSubgroup M g : Subgroup G) : Set G) ≤ V ⊓ conjSubgroup M g := by
  intro k hk
  rw [Subgroup.mem_inf] at hk
  obtain ⟨hkK, hkC⟩ := hk
  let U : Subgroup G := V ⊓ conjSubgroup M g
  let B : Subgroup G := conjSubgroup V g ⊓ M
  have hset : (↑(U ⊔ B) : Set G) = (U : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right U B (le_normalizer_B h)
  have hk' : k ∈ (U : Set G) * (B : Set G) := by
    rw [← hset]
    exact hkK
  obtain ⟨u, huU, b, hbB, hub⟩ := hk'
  change u * b = k at hub
  have hUcomm : ∀ a ∈ U, ∀ c ∈ U, a * c = c * a := by
    intro a ha c hc
    exact Subtype.ext_iff.mp ((h.elemAbelian.1).is_comm.comm ⟨a, ha.1⟩ ⟨c, hc.1⟩)
  have hkCU : k ∈ centralizer (U : Set G) := hkC
  have huCU : u ∈ centralizer (U : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun c hc => (hUcomm u huU c hc).symm)
  have huinvCU : u⁻¹ ∈ centralizer (U : Set G) := (centralizer (U : Set G)).inv_mem huCU
  have hbCU : b ∈ centralizer (U : Set G) := by
    have hb_eq : b = u⁻¹ * k := by
      rw [← hub]
      group
    rw [hb_eq]
    exact (centralizer (U : Set G)).mul_mem huinvCU hkCU
  have hUb : U ≤ V ⊓ centralizer ({b} : Set G) := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hbCU) y hy)
  by_cases hbV : b ∈ centralizer (V : Set G)
  · have hbUB : b ∈ V ⊓ conjSubgroup M g := by
      have hmem : b ∈ (conjSubgroup V g ⊓ M) ⊓ centralizer (V : Set G) := ⟨hbB, hbV⟩
      rw [B_inf_centralizer_eq h hg] at hmem
      exact hmem.1
    have : u * b ∈ V ⊓ conjSubgroup M g :=
      (V ⊓ conjSubgroup M g).mul_mem huU hbUB
    rwa [hub] at this
  · exfalso
    have hcard4 : Nat.card (V ⊓ centralizer ({b} : Set G) : Subgroup G) = 4 :=
      card_centralizer_of_mem_B h hg hbB hbV
    have hle : Nat.card U ≤ Nat.card (V ⊓ centralizer ({b} : Set G) : Subgroup G) :=
      Nat.card_le_card_of_injective
        (fun y : ↥U => (⟨(y : G), hUb y.2⟩ : ↥(V ⊓ centralizer ({b} : Set G))))
        (fun y z hyz => Subtype.ext (by
          have := congrArg Subtype.val hyz
          simpa using this))
    rw [card_U h hg, hcard4] at hle
    omega

theorem cube_mem_K (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) {v i : G}
    (hv : v ∈ V) (hvU : v ∉ V ⊓ conjSubgroup M g) (hi : i ∈ conjSubgroup V g)
    (hiB : i ∉ conjSubgroup V g ⊓ M) :
    (v * i) ^ 3 ∈ (V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) := by
  let U : Subgroup G := V ⊓ conjSubgroup M g
  let B : Subgroup G := conjSubgroup V g ⊓ M
  let K : Subgroup G := U ⊔ B
  let X : Subgroup G := V ⊔ conjSubgroup V g
  let x : G := (v * i) ^ 2
  have hv2 : v * v = 1 := by simpa [pow_two] using h.elemAbelian.2 v hv
  have hi2 : i * i = 1 := by simpa [pow_two] using (h.conj g).elemAbelian.2 i hi
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hi' : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
  have hKM : K ≤ M := sup_le (fun u hu => h.le_M hu.1) (fun b hb => hb.2)
  have hcKcent : (v * i) ^ 3 ∈ centralizer (K : Set G) :=
    cube_mem_centralizer h hg hv hvU hi hiB
  have hcUcent : (v * i) ^ 3 ∈ centralizer (U : Set G) :=
    Subgroup.centralizer_le (fun y hy => Subgroup.mem_sup_left hy) hcKcent
  have hcM : (v * i) ^ 3 ∈ M :=
    h.centralizer_le U (fun y hy => hy.1) (by rw [card_U h hg]; norm_num) hcUcent
  have hx2 : x = v * i * v * i := by
    rw [show x = (v * i) ^ 2 from rfl, pow_two]
    group
  have hxinv : x⁻¹ = i * v * i * v := by
    rw [hx2]
    simp only [mul_inv_rev, inv_inv, hv', hi']
    group
  have hxiconj : x * i * x⁻¹ = (v * i) ^ 3 * v := by
    rw [hxinv, hx2]
    rw [show (v * i * v * i) * i = (v * i * v) * (i * i) by group, hi2, mul_one]
    rw [pow_three]
    group
  have hxX : x ∈ X := by
    have hvX : v ∈ X := Subgroup.mem_sup_left hv
    have hiX : i ∈ X := Subgroup.mem_sup_right hi
    have hx_eq : x = (v * i) * (v * i) := by
      rw [show x = (v * i) ^ 2 from rfl, pow_two]
    rw [hx_eq]
    exact X.mul_mem (X.mul_mem hvX hiX) (X.mul_mem hvX hiX)
  have hxN : x ∈ normalizer (K : Set G) := X_le_normalizer_K h hg hxX
  have hconjB : ∀ b ∈ B, x * b * x⁻¹ ∈ K := by
    intro b hb
    exact (Subgroup.mem_normalizer_iff.mp hxN b).1 (Subgroup.mem_sup_right hb)
  have hVgxM : conjSubgroup V (g * x⁻¹) ≤ M := by
    intro a ha
    rw [← conjSubgroup_conjSubgroup V g x⁻¹] at ha
    rw [mem_conjSubgroup_iff] at ha
    rw [inv_inv] at ha
    set a₀ : G := x⁻¹ * a * x with ha₀def
    have hxax : x * a₀ * x⁻¹ = a := by
      rw [ha₀def]
      group
    have ha₀Vg : a₀ ∈ conjSubgroup V g := ha
    by_cases ha₀B : a₀ ∈ B
    · have hxb : x * a₀ * x⁻¹ ∈ K := hconjB a₀ ha₀B
      rw [hxax] at hxb
      exact hKM hxb
    · have hicos : ∀ y ∈ conjSubgroup V g, y * i ∈ B ∨ y ∈ B := by
        intro y hy
        by_cases hyB : y ∈ B
        · exact Or.inr hyB
        · left
          have hiff := Subgroup.mul_mem_iff_of_index_two
            (H := B.subgroupOf (conjSubgroup V g)) (a := (⟨y, hy⟩ : ↥(conjSubgroup V g)))
            (b := (⟨i, hi⟩ : ↥(conjSubgroup V g)))
            (show (B.subgroupOf (conjSubgroup V g)).index = 2 from relIndex_B h hg)
          have hnode : (⟨y, hy⟩ : ↥(conjSubgroup V g)) ∈ B.subgroupOf (conjSubgroup V g) ↔
              (⟨i, hi⟩ : ↥(conjSubgroup V g)) ∈ B.subgroupOf (conjSubgroup V g) := by
            rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
            exact (iff_false_intro hyB).trans (iff_false_intro hiB).symm
          have hprod : (⟨y, hy⟩ * ⟨i, hi⟩ : ↥(conjSubgroup V g)) ∈
              B.subgroupOf (conjSubgroup V g) := hiff.mpr hnode
          simpa using (Subgroup.mem_subgroupOf.mp hprod)
      rcases hicos a₀ ha₀Vg with ha₀iB | ha₀B'
      · obtain ⟨b, hbB, hb_eq⟩ : ∃ b ∈ B, a₀ = b * i :=
          ⟨a₀ * i, ha₀iB, by rw [mul_assoc, hi2, mul_one]⟩
        have hxb : x * b * x⁻¹ ∈ K := hconjB b hbB
        have heq2 : x * (b * i) * x⁻¹ = (x * b * x⁻¹) * (x * i * x⁻¹) := by group
        have haeq : a = (x * b * x⁻¹) * (x * i * x⁻¹) := by
          rw [← hxax, hb_eq, heq2]
        rw [haeq, hxiconj]
        exact M.mul_mem (hKM hxb) (M.mul_mem hcM (h.le_M hv))
      · exact absurd ha₀B' ha₀B
  have hxbU : ∀ b ∈ B, x * b * x⁻¹ ∈ U := by
    intro b hb
    have hxb_mem : x * b * x⁻¹ ∈ conjSubgroup V (g * x⁻¹) := by
      rw [← conjSubgroup_conjSubgroup V g x⁻¹]
      refine mem_conjSubgroup_iff.mpr ?_
      have e : x⁻¹ * (x * b * x⁻¹) * (x⁻¹)⁻¹ = b := by group
      rw [e]
      exact hb.1
    have hcomm : ⁅V, conjSubgroup V (g * x⁻¹)⁆ = ⊥ := h.comm_eq_bot (g * x⁻¹) hVgxM
    have hcentV : conjSubgroup V (g * x⁻¹) ≤ centralizer (V : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
    have hcentU : x * b * x⁻¹ ∈ centralizer (U : Set G) :=
      Subgroup.centralizer_le (fun y hy => hy.1) (hcentV hxb_mem)
    exact K_inf_centralizer_U_le h hg ⟨hconjB b hb, hcentU⟩
  have hxBU : conjSubgroup B x⁻¹ ≤ U := by
    intro a ha
    have hb : x⁻¹ * a * x ∈ B := by
      simpa using (mem_conjSubgroup_iff.mp ha : x⁻¹ * a * (x⁻¹)⁻¹ ∈ B)
    have h := hxbU (x⁻¹ * a * x) hb
    have e : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
    rwa [e] at h
  have hxBU' : conjSubgroup B x⁻¹ ≤ V ⊓ conjSubgroup V (g * x⁻¹) := by
    refine le_inf ?_ ?_
    · exact hxBU.trans (fun y hy => hy.1)
    · rw [← conjSubgroup_conjSubgroup V g x⁻¹]
      exact E3.conjSubgroup_mono_left x⁻¹ (fun y hy => hy.1)
  have hcardge : 8 ≤ Nat.card (V ⊓ conjSubgroup V (g * x⁻¹) : Subgroup G) := by
    have hle := Nat.card_le_card_of_injective
      (fun y : ↥(conjSubgroup B x⁻¹) =>
        (⟨(y : G), hxBU' y.2⟩ : ↥(V ⊓ conjSubgroup V (g * x⁻¹))))
      (fun y z hyz => Subtype.ext (by
        have := congrArg Subtype.val hyz
        simpa using this))
    rwa [E3.card_conjSubgroup B x⁻¹, card_B h hg] at hle
  have hgxM : g * x⁻¹ ∈ M := by
    by_contra hgx
    have hle2 := h.card_inf_le (g * x⁻¹) hgx
    omega
  have hconjV : conjSubgroup V (g * x⁻¹) = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (by rw [h.normalizer_eq]; exact hgxM)
  have hxiV : x * i * x⁻¹ ∈ V := by
    have hmem : x * i * x⁻¹ ∈ conjSubgroup V (g * x⁻¹) := by
      rw [← conjSubgroup_conjSubgroup V g x⁻¹]
      refine mem_conjSubgroup_iff.mpr ?_
      have e : x⁻¹ * (x * i * x⁻¹) * (x⁻¹)⁻¹ = i := by group
      rw [e]
      exact hi
    rwa [hconjV] at hmem
  have hcV : (v * i) ^ 3 ∈ V := by
    have h := hxiV
    rw [hxiconj] at h
    have h2 : ((v * i) ^ 3 * v) * v⁻¹ ∈ V := V.mul_mem h (V.inv_mem hv)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h2
  by_cases hcU : (v * i) ^ 3 ∈ U
  · exact Subgroup.mem_sup_left hcU
  · exfalso
    have hBU : B ≤ U ⊓ B := by
      intro b hb
      have h1 : ⁅(v * i) ^ 3, b⁆ = 1 :=
        (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hcKcent) b
          (Subgroup.mem_sup_right hb)
      have hcomm : (v * i) ^ 3 * b * ((v * i) ^ 3)⁻¹ * b⁻¹ = 1 := by
        rwa [commutatorElement_def] at h1
      have hcUB : (v * i) ^ 3 * b * ((v * i) ^ 3)⁻¹ * b⁻¹ ∈ U ⊓ B := by
        rw [hcomm]
        exact (U ⊓ B).one_mem
      exact mem_of_commutator_mem h hg hcV hcU hb hcUB
    have hcardle : Nat.card B ≤ Nat.card (U ⊓ B : Subgroup G) :=
      Nat.card_le_card_of_injective
        (fun y : ↥B => (⟨(y : G), hBU y.2⟩ : ↥(U ⊓ B : Subgroup G)))
        (fun y z hyz => Subtype.ext (by
          have := congrArg Subtype.val hyz
          simpa using this))
    rw [card_B h hg, card_U_inf_B h hg] at hcardle
    omega

theorem isQ8Q8S3_X (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) :
    IsQ8Q8S3 ↥(V ⊔ conjSubgroup V g) := by
  let U : Subgroup G := V ⊓ conjSubgroup M g
  let B : Subgroup G := conjSubgroup V g ⊓ M
  let K : Subgroup G := U ⊔ B
  let X : Subgroup G := V ⊔ conjSubgroup V g
  have hKX : K ≤ X := K_le_X h
  have hXN : X ≤ normalizer (K : Set G) := X_le_normalizer_K h hg
  haveI hN : (K.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKX]
    exact hXN
  refine ⟨K.subgroupOf X, hN, ?_, ?_⟩
  · exact isExtraspecialPlus2_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKX).symm
      (isExtraspecialPlus2_K h hg)
  · obtain ⟨v, hv, hvU, hvcos⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and
        (H := U) (K := V)).mp (relIndex_U h hg)
    obtain ⟨i, hi, hiB, hicos⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and
        (H := B) (K := conjSubgroup V g)).mp (relIndex_B h hg)
    have hv2 : v * v = 1 := by simpa [pow_two] using h.elemAbelian.2 v hv
    have hi2 : i * i = 1 := by simpa [pow_two] using (h.conj g).elemAbelian.2 i hi
    have hVK : V ⊓ K ≤ U := by
      intro y hy
      obtain ⟨hyV, hyK⟩ := hy
      have hset : (↑K : Set G) = (U : Set G) * (B : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right U B (le_normalizer_B h)
      have hy' : y ∈ (U : Set G) * (B : Set G) := by rw [← hset]; exact hyK
      obtain ⟨u, hu, b, hb, hub⟩ := hy'
      change u * b = y at hub
      have hbV : b ∈ V := by
        have : b = u⁻¹ * y := by rw [← hub]; group
        rw [this]
        exact V.mul_mem (V.inv_mem hu.1) hyV
      have hbMg : b ∈ conjSubgroup M g := (E3.conjSubgroup_mono_left g h.le_M) hb.1
      have hbU : b ∈ U := ⟨hbV, hbMg⟩
      have : u * b ∈ U := U.mul_mem hu hbU
      rwa [hub] at this
    have hvK : v ∉ K := fun hvK => hvU (hVK ⟨hv, hvK⟩)
    have hAcos : ∀ w ∈ V, w ∈ K ∨ w * v ∈ K := by
      intro w hw
      rcases hvcos w hw with hwv | hwU
      · exact Or.inr (Subgroup.mem_sup_left hwv)
      · exact Or.inl (Subgroup.mem_sup_left hwU)
    have hBcos : ∀ y ∈ conjSubgroup V g, y ∈ K ∨ y * i ∈ K := by
      intro y hy
      rcases hicos y hy with hyi | hyB
      · exact Or.inr (Subgroup.mem_sup_right hyi)
      · exact Or.inl (Subgroup.mem_sup_right hyB)
    have hab3 : (v * i) ^ 3 ∈ K := cube_mem_K h hg hv hvU hi hiB
    have hnot : ¬ ∀ y ∈ V ⊔ conjSubgroup V g, ∃ n : ℕ, y ^ 2 ^ n ∈ K := by
      intro hall
      obtain ⟨n, hn⟩ := hall (v * i)
        (X.mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hi))
      let π : ↥X →* (↥X ⧸ K.subgroupOf X) := QuotientGroup.mk' _
      have hπ1 : ∀ x : ↥X, π x = 1 ↔ (x : G) ∈ K := fun x => QuotientGroup.eq_one_iff x
      let a : ↥X ⧸ K.subgroupOf X :=
        π ⟨v * i, X.mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hi)⟩
      have haeq : a = π (⟨v * i, X.mul_mem (Subgroup.mem_sup_left hv)
          (Subgroup.mem_sup_right hi)⟩ : ↥X) := rfl
      have h3 : a ^ 3 = 1 := by
        dsimp only [a]
        rw [← map_pow]
        exact (hπ1 _).2 hab3
      have h2 : a ^ (2 ^ n) = 1 := by
        dsimp only [a]
        rw [← map_pow]
        exact (hπ1 _).2 hn
      have hdvd : orderOf a ∣ Nat.gcd 3 (2 ^ n) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
      have hcop : Nat.gcd 3 (2 ^ n) = 1 :=
        Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)
      rw [hcop] at hdvd
      have ha1 : a = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)
      have hviK : v * i ∈ K := by
        rw [haeq] at ha1
        exact (hπ1 _).1 ha1
      have hKM : K ≤ M := sup_le (fun u hu => h.le_M hu.1) (fun b hb => hb.2)
      have hviM : v * i ∈ M := hKM hviK
      have hiM : i ∈ M := by
        have hh : v * (v * i) ∈ M := M.mul_mem (h.le_M hv) hviM
        rwa [show v * (v * i) = i by rw [← mul_assoc, hv2, one_mul]] at hh
      exact hiB ⟨hi, hiM⟩
    exact CFSG.Quasithin.H13.VolI.nonempty_sup_quotient_perm_three
      (A := V) (B := conjSubgroup V g) (P := K) hv hi hv2 hi2 hvK hab3 hAcos hBcos hnot

end Cfg1667

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
