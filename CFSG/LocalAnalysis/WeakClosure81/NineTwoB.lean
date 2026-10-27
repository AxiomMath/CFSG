module

public import CFSG.LocalAnalysis.WeakClosure81.NineTwoA
public import CFSG.LocalAnalysis.WeakClosure81.NineSeven
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V K S X : Subgroup G} {p : ℕ}

private theorem nineTwoB_inv_mul_mem_of_not_mem {Q : Type*} [Group Q] {K L : Subgroup Q}
    (hrel : L.relIndex K = 2) {a b : Q} (ha : a ∈ K) (hb : b ∈ K) (haL : a ∉ L)
    (hbL : b ∉ L) : a⁻¹ * b ∈ L := by
  have key := (Subgroup.mul_mem_iff_of_index_two (H := L.subgroupOf K) hrel
    (a := (⟨a, ha⟩ : K)⁻¹) (b := ⟨b, hb⟩)).2 (by
      rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact iff_of_false haL hbL)
  exact Subgroup.mem_subgroupOf.1 key

theorem mul_mul_inv_eq_inv_of_forall_eq_one {Q : Type*} [Group Q] {N : Subgroup Q} [Finite N]
    (hN : N.Normal) {a : Q} (ha : a * a = 1) (hfix : ∀ n ∈ N, a * n * a⁻¹ = n → n = 1) :
    ∀ n ∈ N, a * n * a⁻¹ = n⁻¹ := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have ha'' : a⁻¹ * a⁻¹ = 1 := by rw [ha']; exact ha
  let σ : ↥N → ↥N := fun n => ⟨a * (n : Q) * a⁻¹, hN.conj_mem (n : Q) n.2 a⟩
  let τ : ↥N → ↥N := fun n => σ n * n⁻¹
  have hτinj : Function.Injective τ := by
    intro n m hnm
    have hnm' : (σ n : Q) * (n : Q)⁻¹ = (σ m : Q) * (m : Q)⁻¹ :=
      congrArg Subtype.val hnm
    have hfixnm : a * ((m : Q)⁻¹ * (n : Q)) * a⁻¹ = (m : Q)⁻¹ * (n : Q) := by
      have h1 : (σ m : Q)⁻¹ * (σ n : Q) = (m : Q)⁻¹ * (n : Q) := by
        have h := congrArg (fun t : Q => (σ m : Q)⁻¹ * t * (n : Q)) hnm'
        group at h
        simpa using h
      calc a * ((m : Q)⁻¹ * (n : Q)) * a⁻¹
          = (a * (m : Q) * a⁻¹)⁻¹ * (a * (n : Q) * a⁻¹) := by group
        _ = (σ m : Q)⁻¹ * (σ n : Q) := rfl
        _ = (m : Q)⁻¹ * (n : Q) := h1
    have hmemN : (m : Q)⁻¹ * (n : Q) ∈ N := N.mul_mem (N.inv_mem m.2) n.2
    have h1 := hfix ((m : Q)⁻¹ * (n : Q)) hmemN hfixnm
    apply Subtype.ext
    have h2 : (n : Q) = (m : Q) := by
      have := congrArg (fun t : Q => (m : Q) * t) h1
      simpa [mul_assoc] using this
    exact h2
  have hτsurj : Function.Surjective τ := (Finite.injective_iff_surjective).mp hτinj
  have hσinv : ∀ t : ↥N, σ t = t⁻¹ := by
    intro t
    obtain ⟨n, rfl⟩ := hτsurj t
    apply Subtype.ext
    show a * ((σ n : Q) * (n : Q)⁻¹) * a⁻¹ = ((σ n : Q) * (n : Q)⁻¹)⁻¹
    calc a * ((σ n : Q) * (n : Q)⁻¹) * a⁻¹
        = (a * (σ n : Q) * a⁻¹) * (a * (n : Q)⁻¹ * a⁻¹) := by group
      _ = (n : Q) * ((σ n : Q))⁻¹ := by
          have h1 : a * (σ n : Q) * a⁻¹ = (n : Q) := by
            show a * (a * (n : Q) * a⁻¹) * a⁻¹ = (n : Q)
            rw [show a * (a * (n : Q) * a⁻¹) * a⁻¹ =
                (a * a) * (n : Q) * (a⁻¹ * a⁻¹) by group, ha, ha'', one_mul, mul_one]
          have h2 : a * (n : Q)⁻¹ * a⁻¹ = ((σ n : Q))⁻¹ := by
            show a * (n : Q)⁻¹ * a⁻¹ = (a * (n : Q) * a⁻¹)⁻¹
            group
          rw [h1, h2]
      _ = ((σ n : Q) * (n : Q)⁻¹)⁻¹ := by group
  intro n hn
  have := hσinv ⟨n, hn⟩
  simpa [σ] using congrArg Subtype.val this

theorem nine_two_relIndex (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p)
    {A : Subgroup G} (hA : A ∈ nineOmegaIn V K S) : (pCoreOf 2 K).relIndex A = 2 := by
  have hbase : TwoPTwo K S X p := h.base.toTwoPTwoIrred.toTwoPTwo
  have hAK : A ≤ K := hA.2.trans h.base.sylowTwo.le
  have hsupK : pCoreOf 2 K ⊔ X ≤ K :=
    sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K) h.base.sylowP.le
  have hinf : pCoreOf 2 K ⊓ X = ⊥ := by
    rw [inf_comm]; exact TwoPTwo.sylowP_inf_pCoreOf hbase
  have hrelX : (pCoreOf 2 K).relIndex X = Nat.card X := by
    have h := Subgroup.relIndex_mul_card (H := pCoreOf 2 K) (K := X)
    rw [hinf, Subgroup.card_bot, mul_one] at h
    exact h
  have hoddX : Odd (Nat.card X) := by
    haveI : Fact p.Prime := ⟨h.base.prime⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥X)).mp h.base.sylowP.isPGroup
    rw [hn]
    exact (Nat.Prime.odd_of_ne_two h.base.prime h.base.odd).pow
  have hXodd : Odd ((pCoreOf 2 K).relIndex (pCoreOf 2 K ⊔ X)) := by
    have hsub := Subgroup.relIndex_subgroupOf (H := pCoreOf 2 K) (K := pCoreOf 2 K ⊔ X)
      (L := K) hsupK
    rw [← hsub]
    have hsup' : (pCoreOf 2 K ⊔ X).subgroupOf K =
        (pCoreOf 2 K).subgroupOf K ⊔ X.subgroupOf K :=
      Subgroup.subgroupOf_sup (CFSG.LieType.BorelTits.pCoreOf_le 2 K) h.base.sylowP.le
    rw [hsup']
    haveI : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
    have hRq : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K :=
      CFSG.openPCoreOf_subgroupOf 2 K
    rw [hRq, Subgroup.relIndex_sup_left]
    have hsub2 := Subgroup.relIndex_subgroupOf (H := pCoreOf 2 K) (K := X) (L := K)
      h.base.sylowP.le
    rw [hRq] at hsub2
    rw [hsub2, hrelX]
    exact hoddX
  have hKnorm : K ≤ Subgroup.normalizer ((pCoreOf 2 K ⊔ X : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsupK).mp
      (TwoPTwo.normal_pCoreOf_sup hbase)
  have hAX : A ≤ Subgroup.normalizer ((pCoreOf 2 K ⊔ X : Subgroup G) : Set G) :=
    hAK.trans hKnorm
  have hfaith : ∀ a ∈ A, (∀ x ∈ pCoreOf 2 K ⊔ X, ⁅a, x⁆ ∈ pCoreOf 2 K) →
      a ∈ pCoreOf 2 K := by
    intro a ha hc
    have haK : a ∈ K := hAK ha
    have hsup : a ∈ pCoreOf 2 K ⊔ X :=
      TwoPTwo.mem_sup_of_commutator_mem hbase haK (fun x hx =>
        hc x (Subgroup.mem_sup_right hx))
    have ha2 : a ^ 2 = 1 := (isElemAbelian_of_mem_omegaSet hV.1 hA.1).2 a ha
    exact TwoPTwo.mem_pCoreOf_of_mem_sup hbase hsup (n := 1) (by simpa using ha2)
  have hJnorm : ((pCoreOf 2 K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 K)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  exact seven_six_one_relIndex_eq_two_in (V := V) (H := K) (E := nineE V K)
    (J := pCoreOf 2 K) (A := A) (X := pCoreOf 2 K ⊔ X) (U := A)
    hV.1 hV.2.2 (isElemAbelian_nineE V K).1
    ((nineE_le_pCoreOf V K).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
    (nineE_subgroupOf_normal V K)
    le_rfl hJnorm (fun W _ => inf_le_right) le_sup_left hsupK hAK hAX hXodd hfaith
    ⟨hA.1, hAK⟩ le_rfl

theorem nine_two_centralizer (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p)
    {A : Subgroup G} (hA : A ∈ nineOmegaIn V K S) {x : G} (hx : x ∈ pCoreOf 2 K ⊔ X)
    (hc : ∀ a ∈ A, ⁅x, a⁆ ∈ pCoreOf 2 K) : x ∈ pCoreOf 2 K := by
  have hbase : TwoPTwo K S X p := h.base.toTwoPTwoIrred.toTwoPTwo
  have hAK : A ≤ K := hA.2.trans h.base.sylowTwo.le
  have hxK : x ∈ K := (sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K) h.base.sylowP.le) hx
  have hxN : x ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hxK
  have hAconv : conjSubgroup A x ≤ A ⊔ pCoreOf 2 K := by
    intro y hy
    rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hy
    have hy_eq : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [hy_eq]
    have hcomm : ⁅x * y * x⁻¹, x⁆ ∈ pCoreOf 2 K := by
      have h1 : ⁅x * y * x⁻¹, x⁆ = ⁅x, x * y * x⁻¹⁆⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [h1]
      exact Subgroup.inv_mem _ (hc (x * y * x⁻¹) hy)
    have hconj : x⁻¹ * ⁅x * y * x⁻¹, x⁆ * x ∈ pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff''.mp hxN ⁅x * y * x⁻¹, x⁆).mp hcomm
    have hsplit : x⁻¹ * (x * y * x⁻¹) * x =
        (x⁻¹ * ⁅x * y * x⁻¹, x⁆ * x) * (x * y * x⁻¹) := by
      rw [commutatorElement_def]; group
    rw [hsplit]
    exact (A ⊔ pCoreOf 2 K).mul_mem (Subgroup.mem_sup_right hconj) (Subgroup.mem_sup_left hy)
  have hHle : conjSubgroup (A ⊔ pCoreOf 2 K) x ≤ A ⊔ pCoreOf 2 K := by
    have hsup : conjSubgroup (A ⊔ pCoreOf 2 K) x =
        conjSubgroup A x ⊔ conjSubgroup (pCoreOf 2 K) x := by
      simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_sup]
    rw [hsup]
    refine sup_le hAconv ?_
    have hR : conjSubgroup (pCoreOf 2 K) x = pCoreOf 2 K :=
      CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr hxN
    rw [hR]; exact le_sup_right
  have hHcard : Nat.card ↥(conjSubgroup (A ⊔ pCoreOf 2 K) x) =
      Nat.card ↥(A ⊔ pCoreOf 2 K) := by
    change Nat.card ↥((A ⊔ pCoreOf 2 K).map (MulAut.conj x⁻¹).toMonoidHom) =
      Nat.card ↥(A ⊔ pCoreOf 2 K)
    exact Subgroup.card_map_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
      (MulAut.conj x⁻¹).injective
  have hxnorm : x ∈ Subgroup.normalizer ((A ⊔ pCoreOf 2 K : Subgroup G) : Set G) :=
    CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp
      (Subgroup.eq_of_le_of_card_ge hHle (le_of_eq hHcard.symm))
  obtain ⟨m, hm, j, hj, heq⟩ := seven_three_four_normalizer_in (V := V) (H := K)
    (E := nineE V K) (J := pCoreOf 2 K) (U := A) hV.1 hV.2.2
    (isElemAbelian_nineE V K).1
    ((nineE_le_pCoreOf V K).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
    (nineE_subgroupOf_normal V K) le_rfl
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 K)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
    (fun W _ => inf_le_right) ⟨hA.1, hAK⟩ hxK hxnorm
  have hm_sup : m ∈ pCoreOf 2 K ⊔ X := by
    have hm_eq : m = x * j⁻¹ := by rw [heq]; group
    rw [hm_eq]
    exact (pCoreOf 2 K ⊔ X).mul_mem hx (Subgroup.mem_sup_left (Subgroup.inv_mem _ hj))
  obtain ⟨n, hn⟩ := isPGroup_normalizer_inf hV h hA ⟨m, hm⟩
  have hm2 : m ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hmR : m ∈ pCoreOf 2 K := TwoPTwo.mem_pCoreOf_of_mem_sup hbase hm_sup hm2
  rw [heq]
  exact (pCoreOf 2 K).mul_mem hmR hj

theorem nine_two_inv (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p)
    {A : Subgroup G} (hA : A ∈ nineOmegaIn V K S) {a : G} (ha : a ∈ A)
    (haR : a ∉ pCoreOf 2 K) {x : G} (hx : x ∈ X) : a * x * a⁻¹ * x ∈ pCoreOf 2 K := by
  have hbase : TwoPTwo K S X p := h.base.toTwoPTwoIrred.toTwoPTwo
  have hAK : A ≤ K := hA.2.trans h.base.sylowTwo.le
  have haK : a ∈ K := hAK ha
  have hxK : x ∈ K := h.base.sylowP.le hx
  let Q := ↥K
  let Rq : Subgroup Q := CFSG.pCore 2 Q
  let π : Q →* Q ⧸ Rq := QuotientGroup.mk' Rq
  let N : Subgroup (Q ⧸ Rq) := (X.subgroupOf K).map π
  let aq : Q := ⟨a, haK⟩
  let xq : Q := ⟨x, hxK⟩
  have ha2 : a * a = 1 := by
    simpa [pow_two] using (isElemAbelian_of_mem_omegaSet hV.1 hA.1).2 a ha
  have ha2q : π aq * π aq = 1 := by
    have h : aq * aq = 1 := by
      apply Subtype.ext
      show a * a = 1
      exact ha2
    rw [← map_mul, h, map_one]
  have hNnorm : N.Normal := by
    have hnormal : ((pCoreOf 2 K ⊔ X).subgroupOf K).Normal :=
      TwoPTwo.normal_pCoreOf_sup hbase
    have hsup' : (pCoreOf 2 K ⊔ X).subgroupOf K =
        (pCoreOf 2 K).subgroupOf K ⊔ X.subgroupOf K :=
      Subgroup.subgroupOf_sup (CFSG.LieType.BorelTits.pCoreOf_le 2 K) h.base.sylowP.le
    have hN_eq : N = ((pCoreOf 2 K ⊔ X).subgroupOf K).map π := by
      simp only [N]
      rw [hsup', Subgroup.map_sup]
      have hbot : ((pCoreOf 2 K).subgroupOf K).map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        have hker : MonoidHom.ker π = Rq := QuotientGroup.ker_mk' Rq
        rw [hker]
        exact (CFSG.openPCoreOf_subgroupOf 2 K).le
      rw [hbot, bot_sup_eq]
    rw [hN_eq]
    exact hnormal.map π (QuotientGroup.mk'_surjective Rq)
  have hfix : ∀ n ∈ N, π aq * n * (π aq)⁻¹ = n → n = 1 := by
    intro n hn hne
    obtain ⟨yq, hyq, hyq_eq⟩ := Subgroup.mem_map.mp hn
    have hyX : (yq : G) ∈ X := Subgroup.mem_subgroupOf.mp hyq
    have hyK : (yq : G) ∈ K := h.base.sylowP.le hyX
    have hπ1 : π (aq * yq * aq⁻¹ * yq⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hyq_eq, hne, mul_inv_cancel]
    have hmemRq : aq * yq * aq⁻¹ * yq⁻¹ ∈ Rq := (QuotientGroup.eq_one_iff _).mp hπ1
    have haxmem : a * (yq : G) * a⁻¹ * (yq : G)⁻¹ ∈ pCoreOf 2 K := by
      have hcoe : ((aq * yq * aq⁻¹ * yq⁻¹ : Q) : G)
          = a * (yq : G) * a⁻¹ * (yq : G)⁻¹ := rfl
      rw [← hcoe]
      exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := K) (aq * yq * aq⁻¹ * yq⁻¹)).mpr
        hmemRq
    have hrelA : (pCoreOf 2 K).relIndex A = 2 := nine_two_relIndex hV hm h hA
    have hc : ∀ a' ∈ A, ⁅(yq : G), a'⁆ ∈ pCoreOf 2 K := by
      intro a' ha'
      by_cases ha'R : a' ∈ pCoreOf 2 K
      · have hxa' : (yq : G) * a' * (yq : G)⁻¹ ∈ pCoreOf 2 K :=
          (Subgroup.mem_normalizer_iff.mp
            ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K) hyK) a').mp ha'R
        rw [commutatorElement_def]
        exact (pCoreOf 2 K).mul_mem hxa' (Subgroup.inv_mem _ ha'R)
      · have hr : a⁻¹ * a' ∈ pCoreOf 2 K :=
          nineTwoB_inv_mul_mem_of_not_mem hrelA ha ha' haR ha'R
        have ha'_eq : a' = a * (a⁻¹ * a') := by group
        rw [ha'_eq]
        have hcomm : ⁅(yq : G), a * (a⁻¹ * a')⁆ =
            ⁅(yq : G), a⁆ * (a * ⁅(yq : G), a⁻¹ * a'⁆ * a⁻¹) := by
          rw [commutatorElement_def, commutatorElement_def]; group
        rw [hcomm]
        refine (pCoreOf 2 K).mul_mem ?_ ?_
        · have h1 : ⁅(yq : G), a⁆ = (a * (yq : G) * a⁻¹ * (yq : G)⁻¹)⁻¹ := by
            rw [commutatorElement_def]; group
          rw [h1]
          exact Subgroup.inv_mem _ haxmem
        · have hyr : ⁅(yq : G), a⁻¹ * a'⁆ ∈ pCoreOf 2 K := by
            have hxr : (yq : G) * (a⁻¹ * a') * (yq : G)⁻¹ ∈ pCoreOf 2 K :=
              (Subgroup.mem_normalizer_iff.mp
                ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K) hyK) (a⁻¹ * a')).mp hr
            rw [commutatorElement_def]
            exact (pCoreOf 2 K).mul_mem hxr (Subgroup.inv_mem _ hr)
          exact (Subgroup.mem_normalizer_iff.mp
            ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K) haK)
            ⁅(yq : G), a⁻¹ * a'⁆).mp hyr
    have hyR : (yq : G) ∈ pCoreOf 2 K :=
      nine_two_centralizer hV hm h hA (Subgroup.mem_sup_right hyX) hc
    have hybot : (yq : G) ∈ X ⊓ pCoreOf 2 K := Subgroup.mem_inf.mpr ⟨hyX, hyR⟩
    rw [show X ⊓ pCoreOf 2 K = ⊥ from TwoPTwo.sylowP_inf_pCoreOf hbase, Subgroup.mem_bot]
      at hybot
    have hyq1 : yq = 1 := Subtype.ext hybot
    rw [← hyq_eq, hyq1, map_one]
  have hinv := mul_mul_inv_eq_inv_of_forall_eq_one hNnorm ha2q hfix
  have hxqmem : π xq ∈ N := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
  have hfin := hinv (π xq) hxqmem
  have hmem : aq * xq * aq⁻¹ * xq ∈ Rq := by
    have hπ : π (aq * xq * aq⁻¹ * xq) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hfin, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp hπ
  have hmemG : a * x * a⁻¹ * x ∈ pCoreOf 2 K := by
    have hcoe : ((aq * xq * aq⁻¹ * xq : Q) : G) = a * x * a⁻¹ * x := rfl
    rw [← hcoe]
    exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := K) (aq * xq * aq⁻¹ * xq)).mpr hmem
  exact hmemG

end CFSG.LocalAnalysis.WeakClosure81
