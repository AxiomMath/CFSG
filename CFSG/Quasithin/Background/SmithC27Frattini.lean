module

public import CFSG.Quasithin.Background.SmithC27Star
public import CFSG.Quasithin.Background.SmithC27One

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section General

variable {V : Subgroup G}

omit [Finite G] in
theorem card_sup_mul_card_inf_of_normal' {Γ : Type*} [Group Γ] (A L : Subgroup Γ) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup Γ) * Nat.card (A ⊓ L : Subgroup Γ) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

omit [Finite G] in
theorem card_sup_mul_card_inf_of_le_normalizer' {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal' (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

theorem isSylowTwoOf_sup_of_le_normalizer' {C P : Subgroup G}
    (hPC : P ≤ Subgroup.normalizer (C : Set G)) (hP2 : IsPGroup 2 P)
    (hsyl : IsSylowTwoOf (P ⊓ C) C) : IsSylowTwoOf P (C ⊔ P) := by
  refine ⟨le_sup_right, hP2, ?_⟩
  have h1 := Subgroup.relIndex_mul_card P (C ⊔ P)
  rw [inf_eq_left.2 (le_sup_right : P ≤ C ⊔ P)] at h1
  have h2 := card_sup_mul_card_inf_of_le_normalizer' hPC
  have h3 := Subgroup.relIndex_mul_card (C ⊓ P) C
  rw [inf_eq_left.2 (inf_le_left : C ⊓ P ≤ C)] at h3
  have hpos : 0 < Nat.card ↥(C ⊓ P) := Nat.card_pos
  have hposP : 0 < Nat.card P := Nat.card_pos
  have key : P.relIndex (C ⊔ P) = (C ⊓ P).relIndex C := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hposP hpos)
    calc P.relIndex (C ⊔ P) * (Nat.card P * Nat.card ↥(C ⊓ P))
        = Nat.card ↥(C ⊔ P) * Nat.card ↥(C ⊓ P) := by rw [← h1]; ring
      _ = Nat.card C * Nat.card P := h2
      _ = (C ⊓ P).relIndex C * (Nat.card P * Nat.card ↥(C ⊓ P)) := by rw [← h3]; ring
  have hidx : (P.subgroupOf (C ⊔ P)).index = (C ⊓ P).relIndex C := key
  rw [hidx]
  have hs := hsyl.2.2
  rwa [inf_comm] at hs

omit [Finite G] in
theorem le_normalizer_inf_centralizer' {Y : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) :
    Y ≤ Subgroup.normalizer ((Y ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => ⟨Y.mul_mem (Y.mul_mem hx hc.1) (Y.inv_mem hx),
    C124.conj_mem_centralizer_of_le hY hx hc.2⟩, fun hc => ?_⟩
  have h1 := C124.conj_mem_centralizer_of_le hY (Y.inv_mem hx) hc.2
  exact ⟨by simpa [mul_assoc] using Y.mul_mem (Y.mul_mem (Y.inv_mem hx) hc.1) hx,
    by simpa [mul_assoc] using h1⟩

theorem autOn_le_normalizer_autOn {Y L : Subgroup G}
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) :
    autOn Y V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hYL

theorem exists_mul_of_autOn_mem_normalizer {Y P : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) (hPY : P ≤ Y) (hP : IsPGroup 2 P)
    (hsyl : IsSylowTwoOf (P ⊓ Subgroup.centralizer (V : Set G))
      (Y ⊓ Subgroup.centralizer (V : Set G)))
    {y : G} (hy : y ∈ Y)
    (hyn : conjAct V ⟨y, hY hy⟩ ∈ Subgroup.normalizer (autOn P V : Set (MulAut ↥V))) :
    ∃ c ∈ Y ⊓ Subgroup.centralizer (V : Set G),
      ∃ n ∈ Y ⊓ Subgroup.normalizer (P : Set G), y = c * n := by
  set C : Subgroup G := Y ⊓ Subgroup.centralizer (V : Set G) with hC
  have hCY : Y ≤ Subgroup.normalizer (C : Set G) := le_normalizer_inf_centralizer' hY
  have hPN : P ≤ Subgroup.normalizer (C : Set G) := hPY.trans hCY
  have hPC : P ⊓ C = P ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hC, ← inf_assoc, inf_eq_left.2 hPY]
  set K : Subgroup G := C ⊔ P with hK
  have hKsyl : IsSylowTwoOf P K :=
    isSylowTwoOf_sup_of_le_normalizer' hPN hP (by rw [hPC]; exact hsyl)
  have hconjP : ∀ z ∈ Y, ∀ hz : z ∈ Subgroup.normalizer (V : Set G),
      conjAct V ⟨z, hz⟩ ∈ Subgroup.normalizer (autOn P V : Set (MulAut ↥V)) →
      ∀ p ∈ P, z * p * z⁻¹ ∈ K := by
    intro z hzY hz hzn p hp
    have hpN : p ∈ Subgroup.normalizer (V : Set G) := hY (hPY hp)
    have hzpz : z * p * z⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hzY (hPY hp)) (Y.inv_mem hzY)
    have h1 : conjAct V ⟨z * p * z⁻¹, hY hzpz⟩ ∈ autOn P V := by
      have hp' : conjAct V ⟨p, hpN⟩ ∈ autOn P V := mem_autOn_iff'.2 ⟨_, hp, rfl⟩
      have := (Subgroup.mem_normalizer_iff.1 hzn _).1 hp'
      have e : (⟨z * p * z⁻¹, hY hzpz⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨z, hz⟩ * ⟨p, hpN⟩ * ⟨z, hz⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact this
    obtain ⟨p', hp'P, hp'e⟩ := mem_autOn_iff'.1 h1
    have hmem : z * p * z⁻¹ * (p' : G)⁻¹ ∈ C := by
      refine ⟨Y.mul_mem hzpz (Y.inv_mem (hPY hp'P)), ?_⟩
      have h2 : conjAct V (⟨z * p * z⁻¹, hY hzpz⟩ * p'⁻¹) = 1 := by
        rw [map_mul, map_inv, hp'e, mul_inv_cancel]
      exact (conjAct_eq_one_iff' _).1 h2
    have e2 : z * p * z⁻¹ = (z * p * z⁻¹ * (p' : G)⁻¹) * p' := by group
    rw [e2]
    exact K.mul_mem (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right hp'P)
  have hnormK : ∀ z ∈ Y, ∀ hz : z ∈ Subgroup.normalizer (V : Set G),
      conjAct V ⟨z, hz⟩ ∈ Subgroup.normalizer (autOn P V : Set (MulAut ↥V)) →
      K ≤ K.comap (MulAut.conj z).toMonoidHom := by
    intro z hzY hz hzn
    refine sup_le (fun c hc => ?_) (fun p hp => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hCY hzY) c).1 hc)
    · exact hconjP z hzY hz hzn p hp
  have hyK : y ∈ Subgroup.normalizer (K : Set G) := by
    have hyinv : conjAct V ⟨y⁻¹, hY (Y.inv_mem hy)⟩ ∈
        Subgroup.normalizer (autOn P V : Set (MulAut ↥V)) := by
      have e : conjAct V ⟨y⁻¹, hY (Y.inv_mem hy)⟩ = (conjAct V ⟨y, hY hy⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [e]
      exact Subgroup.inv_mem _ hyn
    apply C124.mem_normalizer_of_conj
    · exact fun k hk => hnormK y hy (hY hy) hyn hk
    · intro k hk
      have := hnormK y⁻¹ (Y.inv_mem hy) (hY (Y.inv_mem hy)) hyinv hk
      simpa [mul_assoc] using this
  have hK2 : IsSylowTwoOf (B6.conjSub y P) K := by
    have := B6.isSylowTwoOf_conjSub hKsyl y
    have hKy : B6.conjSub y K = K := Subgroup.mem_normalizer_iff_map_conj_eq.1 hyK
    rwa [hKy] at this
  obtain ⟨g, hgK, hgy⟩ := B6.isSylowTwoOf_exists_conj hKsyl hK2
  have hz : g⁻¹ * y ∈ Subgroup.normalizer (P : Set G) := by
    apply C124.mem_normalizer_of_conj
    · intro x hx
      have h1 : y * x * y⁻¹ ∈ B6.conjSub y P := by
        rw [B6.mem_conjSub]
        simpa [mul_assoc] using hx
      rw [hgy, B6.mem_conjSub] at h1
      simpa [mul_assoc] using h1
    · intro x hx
      have h1 : g * x * g⁻¹ ∈ B6.conjSub g P := by
        rw [B6.mem_conjSub]
        simpa [mul_assoc] using hx
      rw [← hgy, B6.mem_conjSub] at h1
      simpa [mul_assoc] using h1
  have hgmem : g ∈ ((C : Set G) * (P : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left C P hPN]
    exact hgK
  obtain ⟨c, hc, p, hp, hcp⟩ := hgmem
  have hcp' : c * p = g := hcp
  have hgY : g ∈ Y := by
    rw [← hcp']
    exact Y.mul_mem hc.1 (hPY hp)
  refine ⟨c, hc, p * (g⁻¹ * y), ⟨Y.mul_mem (hPY hp) (Y.mul_mem (Y.inv_mem hgY) hy),
    Subgroup.mul_mem _ (Subgroup.le_normalizer hp) hz⟩, ?_⟩
  rw [← mul_assoc, hcp']
  group

theorem autOn_inf_normalizer_le {Y P : Subgroup G} (hY : Y ≤ Subgroup.normalizer (V : Set G))
    (hPY : P ≤ Y) (hP : IsPGroup 2 P)
    (hsyl : IsSylowTwoOf (P ⊓ Subgroup.centralizer (V : Set G))
      (Y ⊓ Subgroup.centralizer (V : Set G))) :
    autOn Y V ⊓ Subgroup.normalizer (autOn P V : Set (MulAut ↥V)) ≤
      autOn (Y ⊓ Subgroup.normalizer (P : Set G)) V := by
  rintro φ ⟨hφY, hφN⟩
  obtain ⟨y, hyY, rfl⟩ := mem_autOn_iff'.1 hφY
  obtain ⟨c, hc, n, hn, hcn⟩ := exists_mul_of_autOn_mem_normalizer hY hPY hP hsyl hyY hφN
  refine mem_autOn_iff'.2 ⟨⟨n, hY hn.1⟩, hn, ?_⟩
  have hcN : c ∈ Subgroup.normalizer (V : Set G) := hY hc.1
  have e : y = ⟨c, hcN⟩ * ⟨n, hY hn.1⟩ := Subtype.ext hcn
  rw [e, map_mul, (conjAct_eq_one_iff' ⟨c, hcN⟩).2 hc.2, one_mul]

omit [Finite G] in
theorem commutatorElement_mul_center {Γ : Type*} [Group Γ] {c c' : Γ}
    (hc : c ∈ Subgroup.center Γ) (hc' : c' ∈ Subgroup.center Γ) (u w : Γ) :
    ⁅u * c, w * c'⁆ = ⁅u, w⁆ := by
  rw [Subgroup.mem_center_iff] at hc hc'
  simp only [commutatorElement_def]
  calc u * c * (w * c') * (u * c)⁻¹ * (w * c')⁻¹
      = u * (c * (w * c')) * c⁻¹ * u⁻¹ * c'⁻¹ * w⁻¹ := by group
    _ = u * ((w * c') * c) * c⁻¹ * u⁻¹ * c'⁻¹ * w⁻¹ := by rw [← hc (w * c')]
    _ = u * w * (c' * u⁻¹) * c'⁻¹ * w⁻¹ := by group
    _ = u * w * (u⁻¹ * c') * c'⁻¹ * w⁻¹ := by rw [← hc' u⁻¹]
    _ = u * w * u⁻¹ * w⁻¹ := by group

omit [Finite G] in
theorem commutator_mem_pCore_of_mem_oTwoZIn {L : Subgroup G} {z t : G} (hz : z ∈ oTwoZIn L)
    (ht : t ∈ L) : z * t * z⁻¹ * t⁻¹ ∈ pCoreOf 2 L := by
  have hzL : z ∈ L := oTwoZIn_le' L hz
  have hzc : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨z, hzL⟩ ∈
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := mk_mem_center_of_mem_oTwoZIn (y := ⟨z, hzL⟩) hz
  have hc := Subgroup.mem_center_iff.1 hzc ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨t, ht⟩)
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (⟨z, hzL⟩ * ⟨t, ht⟩ * ⟨z, hzL⟩⁻¹ * ⟨t, ht⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  rw [C124.pCoreOf_eq_map_pCore]
  exact ⟨_, h1, rfl⟩

end General

section Hyp

variable {H R M K V : Subgroup G}

theorem starHyp_of_hyp27 (h : Hyp27 H R M K) (hred : IsTwoReducedIn (K ⊔ R) V)
    (hcent : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K)
    (hKV : ¬ K ≤ Subgroup.centralizer (V : Set G)) : StarHyp R K V :=
  ⟨h.norm, h.isPGroup, h.quasi, hred, hcent, h.pCoreOf_sup_le, hKV⟩

theorem Hyp27.starHyp (h : Hyp27 H R M K) :
    StarHyp R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :=
  starHyp_of_hyp27 h (c27_one h).2.2 (c27_one h).2.1 h.not_le_centralizer

theorem sup_inf_normalizer_R_le (h : Hyp27 H R M K) :
    (K ⊔ R) ⊓ Subgroup.normalizer (R : Set G) ≤ M :=
  (inf_le_inf_right _ h.sup_le).trans h.inf_normalizer_le

theorem sup_inf_normalizer_thompsonJ_le (h : Hyp27 H R M K) :
    (K ⊔ R) ⊓ Subgroup.normalizer (thompsonJ R : Set G) ≤ M := by
  have hJ1 : thompsonJ R ≠ ⊥ := QuasithinUnique.Setup.thompsonJ_ne_bot h.isPGroup h.R_ne_bot
  have h1 : (K ⊔ R) ⊓ Subgroup.normalizer (thompsonJ R : Set G) ≤
      H ⊓ Subgroup.normalizer (thompsonJ R : Set G) := inf_le_inf_right _ h.sup_le
  have h2 : H ⊓ Subgroup.normalizer (thompsonJ R : Set G) ≤ cgsIn H R :=
    le_iSup_of_le (thompsonJ R) (le_iSup_of_le (thompsonJ_le_self R)
      (le_iSup_of_le hJ1 (le_iSup_of_le (QuasithinUnique.Setup.characteristic_thompsonJ R)
        le_rfl)))
  exact (h1.trans h2).trans h.hyp.cgs

end Hyp

section StepStar

variable {H R M K V : Subgroup G}

theorem autOn_inf_normalizer_thompsonJ (hs : StarHyp R K V) :
    autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn (thompsonJ R) V : Set (MulAut ↥V)) =
      autOn ((K ⊔ R) ⊓ Subgroup.normalizer (thompsonJ R : Set G)) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 (K ⊔ R) with hQ
  set J := thompsonJ R with hJ
  set P : Subgroup G := Q ⊔ J with hP
  have hJR : J ≤ R := thompsonJ_le_self R
  have hPR : P ≤ R := sup_le hs.core hJR
  have hPX : P ≤ K ⊔ R := hPR.trans le_sup_right
  have hP2 : IsPGroup 2 P := hs.pgroup.to_le hPR
  have hJQ : J ≤ Subgroup.normalizer (Q : Set G) :=
    (hJR.trans le_sup_right).trans (le_normalizer_pCoreOf 2 _)
  have hPC : P ⊓ Subgroup.centralizer (V : Set G) = Q := by
    apply le_antisymm
    · rw [hQ, hs.pCore_eq_inf]
      exact inf_le_inf_right _ hPR
    · exact le_inf le_sup_left hs.pCore_le_centralizer
  have hsyl : IsSylowTwoOf (P ⊓ Subgroup.centralizer (V : Set G))
      ((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [hPC]
    exact hs.centralizer_isSylow
  have hPJ : autOn P V = autOn J V := by
    refine le_antisymm ?_ (autOn_mono' le_sup_right)
    intro φ hφ
    obtain ⟨x, hx, rfl⟩ := mem_autOn_iff'.1 hφ
    obtain ⟨q, hq, j, hj, hqj⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hJQ).1 hx
    have hqN : q ∈ Subgroup.normalizer (V : Set G) := hs.le_normalizer_V (pCoreOf_le 2 _ hq)
    have hjN : j ∈ Subgroup.normalizer (V : Set G) := hs.R_le_normalizer_V (hJR hj)
    have e : x = ⟨q, hqN⟩ * ⟨j, hjN⟩ := Subtype.ext hqj
    rw [e, map_mul, (conjAct_eq_one_iff' ⟨q, hqN⟩).2 (hs.pCore_le_centralizer hq), one_mul]
    exact mem_autOn_iff'.2 ⟨_, hj, rfl⟩
  have hJP : J = thompsonJ P := thompsonJ_eq_of_le le_sup_right hPR
  apply le_antisymm
  · have h1 := autOn_inf_normalizer_le hs.le_normalizer_V hPX hP2 hsyl
    rw [hPJ] at h1
    refine h1.trans (autOn_mono' (inf_le_inf_left _ ?_))
    intro n hn
    rw [hJP, Subgroup.mem_normalizer_iff_map_conj_eq]
    exact cjSub_thompsonJ hn
  · exact le_inf (autOn_mono' inf_le_left) (autOn_le_normalizer_autOn inf_le_right)

theorem normalizer_J_star_le (h : Hyp27 H R M K) (hs : StarHyp R K V) :
    autOn K V ⊓ Subgroup.normalizer (autOn (thompsonJ R) V : Set (MulAut ↥V)) ≤
      autOn (M ⊓ K) V := by
  rintro φ ⟨hφK, hφN⟩
  have h1 : φ ∈ autOn ((K ⊔ R) ⊓ Subgroup.normalizer (thompsonJ R : Set G)) V := by
    rw [← autOn_inf_normalizer_thompsonJ hs]
    exact ⟨autOn_mono' le_sup_left hφK, hφN⟩
  have h2 : φ ∈ autOn (M ⊓ (K ⊔ R)) V :=
    autOn_mono' (le_inf (sup_inf_normalizer_thompsonJ_le h) inf_le_left) h1
  rw [hs.autOn_inf_M (h.R_le_M)]
  exact ⟨h2, hφK⟩

theorem pCore_K_le_M (h : Hyp27 H R M K) (hs : StarHyp R K V) : pCoreOf 2 K ≤ M :=
  hs.pCore_K_le_pCore.trans (hs.core.trans (h.R_le_M))

theorem autOn_MK_lt (h : Hyp27 H R M K) (hs : StarHyp R K V) :
    autOn (M ⊓ K) V < autOn K V := by
  refine lt_of_le_of_ne (autOn_mono' inf_le_right) fun heq => h.not_le ?_
  have hO2M := pCore_K_le_M h hs
  have hdec : ∀ a ∈ K, ∃ m ∈ M ⊓ K, m⁻¹ * a ∈ oTwoZIn K := by
    intro a ha
    have haN : a ∈ Subgroup.normalizer (V : Set G) := hs.K_le_normalizer_V ha
    have h1 : conjAct V ⟨a, haN⟩ ∈ autOn (M ⊓ K) V := by
      rw [heq]
      exact mem_autOn_iff'.2 ⟨_, ha, rfl⟩
    obtain ⟨n, hn, hne⟩ := mem_autOn_iff'.1 h1
    refine ⟨n, hn, hs.inf_centralizer_le ⟨K.mul_mem (K.inv_mem hn.2) ha, ?_⟩⟩
    have h2 : conjAct V (n⁻¹ * ⟨a, haN⟩) = 1 := by rw [map_mul, map_inv, hne, inv_mul_cancel]
    exact (conjAct_eq_one_iff' _).1 h2
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set D : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := ((M ⊓ K).subgroupOf K).map π with hD
  have hcomm : commutator (↥K ⧸ CFSG.pCore 2 ↥K) = ⊤ := Group.isPerfect_def.mp h.quasi.1
  have hDtop : (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ≤ D := by
    rw [← hcomm, commutator, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) y
    obtain ⟨m, hm, hmz⟩ := hdec a a.2
    obtain ⟨m', hm', hm'z⟩ := hdec b b.2
    have ea : a = ⟨m, hm.2⟩ * ⟨m⁻¹ * a, oTwoZIn_le' K hmz⟩ := Subtype.ext (by simp)
    have eb : b = ⟨m', hm'.2⟩ * ⟨m'⁻¹ * b, oTwoZIn_le' K hm'z⟩ := Subtype.ext (by simp)
    have hc1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ⟨m⁻¹ * a, oTwoZIn_le' K hmz⟩ ∈
        Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) :=
      mk_mem_center_of_mem_oTwoZIn (y := ⟨_, oTwoZIn_le' K hmz⟩) hmz
    have hc2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ⟨m'⁻¹ * b, oTwoZIn_le' K hm'z⟩ ∈
        Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) :=
      mk_mem_center_of_mem_oTwoZIn (y := ⟨_, oTwoZIn_le' K hm'z⟩) hm'z
    rw [ea, eb, map_mul, map_mul, commutatorElement_mul_center hc1 hc2,
      ← map_commutatorElement]
    refine ⟨_, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (M ⊓ K).mul_mem ((M ⊓ K).mul_mem ((M ⊓ K).mul_mem hm hm') ((M ⊓ K).inv_mem hm))
      ((M ⊓ K).inv_mem hm')
  intro k hk
  obtain ⟨x, hx, hxk⟩ := hDtop (Subgroup.mem_top (π ⟨k, hk⟩))
  have h1 : x⁻¹ * ⟨k, hk⟩ ∈ CFSG.pCore 2 ↥K := QuotientGroup.eq.1 hxk
  have h2 : ((x⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ M :=
    hO2M (by rw [C124.pCoreOf_eq_map_pCore]; exact ⟨_, h1, rfl⟩)
  have h3 : (x : G) ∈ M := (Subgroup.mem_subgroupOf.1 hx).1
  have e : k = (x : G) * ((x⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
  rw [e]
  exact M.mul_mem h3 h2

theorem autOn_MK_ne (h : Hyp27 H R M K) (hs : StarHyp R K V) : autOn (M ⊓ K) V ≠ autOn K V :=
  (autOn_MK_lt h hs).ne

theorem pCore_MK_star_le_R_star (h : Hyp27 H R M K) (hs : StarHyp R K V) :
    pCoreOf 2 (autOn (M ⊓ K) V) ≤ autOn R V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := pCoreOf 2 (autOn (M ⊓ K) V) with hA
  set N := Subgroup.normalizer (V : Set G) with hN
  set Phat : Subgroup G := ((A.comap (conjAct V)).map N.subtype) ⊓ (M ⊓ K) with hPhat
  have hO2M := pCore_K_le_M h hs
  have hmem : ∀ {x : G}, x ∈ Phat ↔ x ∈ M ⊓ K ∧ ∃ hx : x ∈ N, conjAct V ⟨x, hx⟩ ∈ A := by
    intro x
    constructor
    · rintro ⟨⟨n, hn, rfl⟩, hx⟩
      exact ⟨hx, n.2, hn⟩
    · rintro ⟨hx, hxN, hxA⟩
      exact ⟨⟨⟨x, hxN⟩, hxA, rfl⟩, hx⟩
  have hPK : Phat ≤ K := inf_le_right.trans inf_le_right
  have hPN : Phat ≤ N := hPK.trans hs.K_le_normalizer_V
  have hYMK : M ⊓ (K ⊔ R) ≤ Subgroup.normalizer ((M ⊓ K : Subgroup G) : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy.1, hs.le_normalizer hy.2⟩
  have hYnorm : M ⊓ (K ⊔ R) ≤ Subgroup.normalizer (Phat : Set G) := by
    intro y hy
    have hyN : y ∈ N := hs.le_normalizer_V hy.2
    have hyA : conjAct V ⟨y, hyN⟩ ∈ Subgroup.normalizer (A : Set (MulAut ↥V)) := by
      have h1 : conjAct V ⟨y, hyN⟩ ∈ Subgroup.normalizer (autOn (M ⊓ K) V : Set (MulAut ↥V)) :=
        autOn_le_normalizer_autOn hYMK (mem_autOn_iff'.2 ⟨_, hy, rfl⟩)
      exact normalizer_le_normalizer_pCoreOf 2 _ h1
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxMK, hxN, hxA⟩ := hmem.1 hx
    refine hmem.2 ⟨(Subgroup.mem_normalizer_iff.1 (hYMK hy) x).1 hxMK,
      N.mul_mem (N.mul_mem hyN hxN) (N.inv_mem hyN), ?_⟩
    have e : (⟨y * x * y⁻¹, N.mul_mem (N.mul_mem hyN hxN) (N.inv_mem hyN)⟩ : ↥N) =
        ⟨y, hyN⟩ * ⟨x, hxN⟩ * ⟨y, hyN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hyA _).1 hxA
  have hO2P : pCoreOf 2 K ≤ Phat := by
    intro x hx
    have hxK : x ∈ K := pCoreOf_le 2 K hx
    refine hmem.2 ⟨⟨hO2M hx, hxK⟩, hs.K_le_normalizer_V hxK, ?_⟩
    rw [(conjAct_eq_one_iff' _).2 (hs.pCore_K_le_centralizer hx)]
    exact A.one_mem
  obtain ⟨T₀, hT₀, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup G) ≤ Phat)
    (IsPGroup.of_card (n := 0) (by simp))
  have hO2T : pCoreOf 2 K ≤ T₀ := by
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 Phat :=
      le_pCoreOf_of_le_normalizer 2 hO2P (hPK.trans (le_normalizer_pCoreOf 2 K))
        (pCoreOf_isPGroup 2 K)
    exact h1.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT₀)
  have hT₀C : IsSylowTwoOf (T₀ ⊓ Subgroup.centralizer (V : Set G))
      (Phat ⊓ Subgroup.centralizer (V : Set G)) := by
    have := A4.isSylowTwoOf_inf_normal hT₀ inf_le_left (le_normalizer_inf_centralizer' hPN)
    rwa [← inf_assoc, inf_eq_left.2 hT₀.1] at this
  have hsylstar : IsSylowTwoOf (autOn T₀ V) (autOn Phat V) :=
    (isSylowTwoOf_iff_autOn hPN hT₀.1 hT₀.2.1 hT₀C).1 hT₀
  have hPhatA : autOn Phat V = A := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨n, hn, rfl⟩ := mem_autOn_iff'.1 hφ
      obtain ⟨-, hnN, hnA⟩ := hmem.1 hn
      exact hnA
    · intro φ hφ
      have hφMK : φ ∈ autOn (M ⊓ K) V := pCoreOf_le 2 _ hφ
      obtain ⟨n, hn, rfl⟩ := mem_autOn_iff'.1 hφMK
      exact mem_autOn_iff'.2 ⟨n, hmem.2 ⟨hn, n.2, hφ⟩, rfl⟩
  have hT₀A : autOn T₀ V = A := by
    rw [← hPhatA]
    refine le_antisymm (autOn_mono' hT₀.1) ?_
    have hA2 : IsPGroup 2 ↥(autOn Phat V) := by
      rw [hPhatA]
      exact pCoreOf_isPGroup 2 _
    obtain ⟨k, hk⟩ := hA2.index ((autOn T₀ V).subgroupOf (autOn Phat V))
    have hk0 : k = 0 := by
      by_contra hk0
      exact hsylstar.2.2 (hk ▸ dvd_pow_self 2 hk0)
    rw [hk0, pow_zero, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hk
    exact hk
  have hT₀n : Phat ≤ Subgroup.normalizer (T₀ : Set G) := by
    intro x hx
    obtain ⟨hxMK, hxN, hxA⟩ := hmem.1 hx
    have hxT : conjAct V ⟨x, hxN⟩ ∈ autOn T₀ V := by
      rw [hT₀A]
      exact hxA
    obtain ⟨t, ht, hte⟩ := mem_autOn_iff'.1 hxT
    have hz : (t : G)⁻¹ * x ∈ oTwoZIn K := by
      refine hs.inf_centralizer_le ⟨K.mul_mem (K.inv_mem (hPK (hT₀.1 ht))) hxMK.2, ?_⟩
      have h2 : conjAct V (t⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hte, inv_mul_cancel]
      exact (conjAct_eq_one_iff' _).1 h2
    have hzT : (t : G)⁻¹ * x ∈ Subgroup.normalizer (T₀ : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun s hs' => ?_
      have hc := commutator_mem_pCore_of_mem_oTwoZIn hz (hPK (hT₀.1 hs'))
      have e : ((t : G)⁻¹ * x) * s * ((t : G)⁻¹ * x)⁻¹ =
          (((t : G)⁻¹ * x) * s * ((t : G)⁻¹ * x)⁻¹ * s⁻¹) * s := by group
      rw [e]
      exact T₀.mul_mem (hO2T hc) hs'
    have e : x = (t : G) * ((t : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer ht) hzT
  have hT₀O : T₀ ≤ pCoreOf 2 Phat := le_pCoreOf_of_le_normalizer 2 hT₀.1 hT₀n hT₀.2.1
  have hSR : pCoreOf 2 Phat ≤ R := by
    refine le_of_isSignalizer_of_isTwoRadicalIn (h.isTwoRadicalIn_sup)
      ⟨(pCoreOf_le 2 _).trans (hPK.trans le_sup_left), pCoreOf_isPGroup 2 _, ?_⟩
    intro y hy
    exact normalizer_le_normalizer_pCoreOf 2 _
      (hYnorm ⟨sup_inf_normalizer_R_le h hy, hy.1⟩)
  rw [← hT₀A]
  exact autOn_mono' (hT₀O.trans hSR)

end StepStar

end CFSG.Quasithin.SmithC27
