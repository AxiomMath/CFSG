module

public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Open Subgroup

variable {Q : Type*} [Group Q]

theorem le_closure_commutator_of_mem_normalizer {L : Subgroup Q} (hL : IsQuasisimple ↥L) {g : Q}
    (hgL : g ∈ normalizer (L : Set Q)) (hg : g ∉ centralizer (L : Set Q)) :
    L ≤ closure {z | ∃ y ∈ L, z = y * g * y⁻¹ * g⁻¹} := by
  let M : Subgroup Q := closure {z | ∃ y ∈ L, z = y * g * y⁻¹ * g⁻¹}
  have hgen : ∀ y ∈ L, y * g * y⁻¹ * g⁻¹ ∈ M := fun y hy =>
    Subgroup.subset_closure ⟨y, hy, rfl⟩
  have hconjL : ∀ y ∈ L, g * y * g⁻¹ ∈ L := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hgL y).mp hy
  have hMle : M ≤ L := by
    rw [Subgroup.closure_le]
    rintro z ⟨y, hy, rfl⟩
    have h1 : g * y⁻¹ * g⁻¹ ∈ L := hconjL y⁻¹ (L.inv_mem hy)
    have h2 : y * (g * y⁻¹ * g⁻¹) ∈ L := L.mul_mem hy h1
    rwa [show y * g * y⁻¹ * g⁻¹ = y * (g * y⁻¹ * g⁻¹) from by group]
  have hconj : ∀ x ∈ L, ∀ m ∈ M, x * m * x⁻¹ ∈ M := by
    intro x hx m hm
    induction hm using Subgroup.closure_induction with
    | mem z hz =>
        obtain ⟨y, hy, rfl⟩ := hz
        rw [show x * (y * g * y⁻¹ * g⁻¹) * x⁻¹ =
          (x * y * g * (x * y)⁻¹ * g⁻¹) * (x * g * x⁻¹ * g⁻¹)⁻¹ by group]
        exact M.mul_mem (hgen (x * y) (L.mul_mem hx hy)) (M.inv_mem (hgen x hx))
    | one => simpa using M.one_mem
    | mul a b _ _ ha hb =>
        rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group]
        exact M.mul_mem ha hb
    | inv a _ ha =>
        rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group]
        exact M.inv_mem ha
  have hnormal : (M.subgroupOf L).Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hconj (x : Q) x.2 (n : Q) hn
  haveI : (M.subgroupOf L).Normal := hnormal
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hL (M.subgroupOf L)
    with hcent | htop
  · exfalso
    have hcent' : ∀ y : ↥L, (⟨(y : Q) * g * (y : Q)⁻¹ * g⁻¹, hMle (hgen (y : Q) y.2)⟩ : ↥L) ∈
        Subgroup.center ↥L := fun y =>
      hcent (Subgroup.mem_subgroupOf.mpr (hgen (y : Q) y.2))
    let φ : ↥L →* ↥L :=
      { toFun := fun y => ⟨(y : Q) * g * (y : Q)⁻¹ * g⁻¹, hMle (hgen (y : Q) y.2)⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun x y => by
          have hcommxy := Subgroup.mem_center_iff.mp (hcent' y) x
          have hx : (x : Q) * ((y : Q) * g * (y : Q)⁻¹ * g⁻¹) * (x : Q)⁻¹ =
              (y : Q) * g * (y : Q)⁻¹ * g⁻¹ := by
            have hval : (x : Q) * ((y : Q) * g * (y : Q)⁻¹ * g⁻¹) =
                ((y : Q) * g * (y : Q)⁻¹ * g⁻¹) * (x : Q) :=
              congrArg Subtype.val hcommxy
            rw [hval]
            group
          have hcommval : ((x : Q) * g * (x : Q)⁻¹ * g⁻¹) *
                ((y : Q) * g * (y : Q)⁻¹ * g⁻¹) =
              ((y : Q) * g * (y : Q)⁻¹ * g⁻¹) *
                ((x : Q) * g * (x : Q)⁻¹ * g⁻¹) :=
            congrArg Subtype.val
              (Subgroup.mem_center_iff.mp (hcent' y) ⟨_, hMle (hgen (x : Q) x.2)⟩)
          apply Subtype.ext
          calc (↑(x * y) : Q) * g * ↑(x * y)⁻¹ * g⁻¹
              = ((x : Q) * ((y : Q) * g * (y : Q)⁻¹ * g⁻¹) * (x : Q)⁻¹) *
                  ((x : Q) * g * (x : Q)⁻¹ * g⁻¹) := by
                push_cast
                group
            _ = ((y : Q) * g * (y : Q)⁻¹ * g⁻¹) *
                  ((x : Q) * g * (x : Q)⁻¹ * g⁻¹) := by rw [hx]
            _ = ((x : Q) * g * (x : Q)⁻¹ * g⁻¹) *
                  ((y : Q) * g * (y : Q)⁻¹ * g⁻¹) := hcommval.symm }
    have hrange : φ.range ≤ Subgroup.center ↥L := by
      rintro _ ⟨y, rfl⟩
      exact hcent' y
    haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hL.1
    haveI : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
    have hbot : φ.range = ⊥ :=
      CFSG.ComponentClassification.Quasisimple.perfect_le_center_eq_bot φ.range hrange
    have hone : φ = 1 := by
      ext y
      have hy : φ y ∈ φ.range := ⟨y, rfl⟩
      rw [hbot] at hy
      simpa using hy
    refine hg ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : (φ ⟨y, hy⟩ : ↥L) = 1 := by
      rw [hone]
      rfl
    have h2 : y * g * y⁻¹ * g⁻¹ = 1 := by
      have := congrArg Subtype.val h1
      simpa [φ] using this
    calc y * g = y * g * y⁻¹ * g⁻¹ * (g * y) := by group
      _ = g * y := by rw [h2, one_mul]
  · intro y hy
    have hyM : (⟨y, hy⟩ : ↥L) ∈ M.subgroupOf L := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hyM

theorem exists_pow_commute_iff_dvd {L : Subgroup Q} (x : ↥L ⧸ center ↥L) :
    ∃ w ∈ L, ∀ k : ℕ, (∀ z ∈ L, w ^ k * z = z * w ^ k) ↔ orderOf x ∣ k := by
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨(w₀ : Q), w₀.2, fun k => ?_⟩
  rw [orderOf_dvd_iff_pow_eq_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using (h (g : Q) g.2).symm
  · intro h z hz
    have h1 := congrArg Subtype.val (h ⟨z, hz⟩)
    simp only [Subgroup.coe_mul, Subtype.coe_mk, Subgroup.coe_pow] at h1
    exact h1.symm

theorem commute_of_mul_mem {L K : Subgroup Q} (hL : IsQuasisimple ↥L)
    (hLK : ∀ z ∈ L, ∀ k ∈ K, z * k * z⁻¹ ∈ K) (hK : ¬ L ≤ K) {a : Q} (ha : a * a = 1)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x) {y : Q} (hy : y ∈ L)
    (hyK : a * y⁻¹ * a * y ∈ K) : ∀ z ∈ L, y * z = z * y := by
  have hcommK : ∀ z ∈ L, y * z * y⁻¹ * z⁻¹ ∈ K := by
    intro z hz
    have hzK : z * (a * y⁻¹ * a * y)⁻¹ * z⁻¹ ∈ K := by
      have h := K.inv_mem (hLK z hz (a * y⁻¹ * a * y) hyK)
      rwa [show (z * (a * y⁻¹ * a * y) * z⁻¹)⁻¹ =
        z * (a * y⁻¹ * a * y)⁻¹ * z⁻¹ from by group] at h
    have hprod : (a * y⁻¹ * a * y) * z * (a * y⁻¹ * a * y)⁻¹ * z⁻¹ ∈ K := by
      have h := K.mul_mem hyK hzK
      rwa [show (a * y⁻¹ * a * y) * (z * (a * y⁻¹ * a * y)⁻¹ * z⁻¹) =
        (a * y⁻¹ * a * y) * z * (a * y⁻¹ * a * y)⁻¹ * z⁻¹ from by group] at h
    have hc : (a * y⁻¹ * a) * (y * z * y⁻¹) = (y * z * y⁻¹) * (a * y⁻¹ * a) :=
      (hLa (y * z * y⁻¹) (L.mul_mem (L.mul_mem hy hz) (L.inv_mem hy)) y⁻¹
        (L.inv_mem hy)).symm
    have heq : (a * y⁻¹ * a * y) * z * (a * y⁻¹ * a * y)⁻¹ * z⁻¹ =
        y * z * y⁻¹ * z⁻¹ := by
      calc (a * y⁻¹ * a * y) * z * (a * y⁻¹ * a * y)⁻¹ * z⁻¹
          = (a * y⁻¹ * a) * (y * z * y⁻¹) * (a * y⁻¹ * a)⁻¹ * z⁻¹ := by group
        _ = (y * z * y⁻¹) * (a * y⁻¹ * a) * (a * y⁻¹ * a)⁻¹ * z⁻¹ := by rw [hc]
        _ = y * z * y⁻¹ * z⁻¹ := by group
    rwa [heq] at hprod
  have hKLnormal : (K.subgroupOf L).Normal := by
    refine ⟨fun k hk l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    simpa using hLK (l : Q) l.2 (k : Q) hk
  haveI : (K.subgroupOf L).Normal := hKLnormal
  have hKLne : K.subgroupOf L ≠ ⊤ := fun h => hK (Subgroup.subgroupOf_eq_top.mp h)
  have hKLle : K.subgroupOf L ≤ Subgroup.center ↥L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hL (K.subgroupOf L) hKLne
  let ψ : ↥L →* ↥L :=
    { toFun := fun z => ⟨y * (z : Q) * y⁻¹ * (z : Q)⁻¹,
        L.mul_mem (L.mul_mem (L.mul_mem hy z.2) (L.inv_mem hy)) (L.inv_mem z.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun z₁ z₂ => by
        have hcent : (⟨y * (z₂ : Q) * y⁻¹ * (z₂ : Q)⁻¹,
            L.mul_mem (L.mul_mem (L.mul_mem hy z₂.2) (L.inv_mem hy)) (L.inv_mem z₂.2)⟩ : ↥L) ∈
            Subgroup.center ↥L :=
          hKLle (Subgroup.mem_subgroupOf.mpr (hcommK (z₂ : Q) z₂.2))
        have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcent z₁)
        simp only [Subgroup.coe_mul, Subtype.coe_mk] at hc
        apply Subtype.ext
        calc y * ((z₁ : Q) * (z₂ : Q)) * y⁻¹ * ((z₁ : Q) * (z₂ : Q))⁻¹
            = (y * (z₁ : Q) * y⁻¹ * (z₁ : Q)⁻¹) *
                ((z₁ : Q) * (y * (z₂ : Q) * y⁻¹ * (z₂ : Q)⁻¹) * (z₁ : Q)⁻¹) := by
              push_cast
              group
          _ = (y * (z₁ : Q) * y⁻¹ * (z₁ : Q)⁻¹) *
                (y * (z₂ : Q) * y⁻¹ * (z₂ : Q)⁻¹) := by
              rw [hc]
              group }
  have hrange : ψ.range ≤ Subgroup.center ↥L := by
    rintro _ ⟨z, rfl⟩
    exact hKLle (Subgroup.mem_subgroupOf.mpr (hcommK (z : Q) z.2))
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hL.1
  haveI : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  have hbot : ψ.range = ⊥ :=
    CFSG.ComponentClassification.Quasisimple.perfect_le_center_eq_bot ψ.range hrange
  have hone : ψ = 1 := by
    ext z
    have hz : ψ z ∈ ψ.range := ⟨z, rfl⟩
    rw [hbot] at hz
    simpa using hz
  intro z hz
  have h1 : (ψ ⟨z, hz⟩ : ↥L) = 1 := by
    rw [hone]
    rfl
  have h2 : y * z * y⁻¹ * z⁻¹ = 1 := by
    have := congrArg Subtype.val h1
    simpa [ψ] using this
  calc y * z = y * z * y⁻¹ * z⁻¹ * (z * y) := by group
    _ = z * y := by rw [h2, one_mul]

theorem exists_orbit_data [Finite Q] {a : Q} {L A : Subgroup Q} (ha : orderOf a = 2)
    (hL : IsComponentOf L ⊤) (hA : Nat.card A = 4) (hA2 : IsElemAbelian 2 A) (haA : a ∈ A)
    (hAL : A ⊓ centralizer (L : Set Q) = ⊥) (haL : a ∉ normalizer (L : Set Q)) :
    (∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x) ∧
      ∃ b ∈ A, b * b = 1 ∧ a * b = b * a ∧
        ((b ∈ normalizer (L : Set Q) ∧ L ≤ closure {z | ∃ y ∈ L, z = y * b * y⁻¹ * b⁻¹}) ∨
          ((∀ x ∈ L, ∀ y ∈ L, x * (b * y * b) = (b * y * b) * x) ∧
            ∀ x ∈ L, ∀ y ∈ L, x * ((a * b) * y * (a * b)) = ((a * b) * y * (a * b)) * x)) := by
  have haa : a * a = 1 := by
    have h : a ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [ha])
    simpa [pow_two] using h
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hconj_comm : ∀ g : Q, g ∉ normalizer (L : Set Q) → g⁻¹ = g →
      ∀ x ∈ L, ∀ y ∈ L, x * (g * y * g) = (g * y * g) * x := by
    intro g hg hginv x hx y hy
    have hcomp : IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ :=
      (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL
    have hne : L.map (MulAut.conj g).toMonoidHom ≠ L := fun h =>
      hg (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    have hne' : L ≠ L.map (MulAut.conj g).toMonoidHom := fun h => hne h.symm
    have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne L _ hL hcomp hne'
    have hle : L ≤ Subgroup.centralizer
        ((L.map (MulAut.conj g).toMonoidHom : Subgroup Q) : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hmem : (MulAut.conj g) y ∈ L.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hy
    have h := (Subgroup.mem_centralizer_iff.mp (hle hx)) ((MulAut.conj g) y) hmem
    rw [show g * y * g = (MulAut.conj g) y by rw [MulAut.conj_apply, hginv]]
    exact h.symm
  classical
  haveI : Fintype ↥A := Fintype.ofFinite _
  have hcardA : Fintype.card ↥A = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hA
  have hane : (⟨a, haA⟩ : ↥A) ≠ 1 := by
    intro h
    have ha1 : a = 1 := congrArg Subtype.val h
    rw [ha1, orderOf_one] at ha
    omega
  obtain ⟨b0, hb0ne1, hb0nea⟩ : ∃ b0 : ↥A, b0 ≠ 1 ∧ b0 ≠ ⟨a, haA⟩ := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hsub : (Finset.univ : Finset ↥A) ⊆ {1, (⟨a, haA⟩ : ↥A)} := by
      intro b _
      by_cases h1 : b = 1
      · simp [h1]
      · have h2 : b = ⟨a, haA⟩ := h b h1
        simp [h2]
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, hcardA] at hle
    have htwo : ({1, (⟨a, haA⟩ : ↥A)} : Finset ↥A).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hane.symm), Finset.card_singleton]
    rw [htwo] at hle
    omega
  have hb0A : (b0 : Q) ∈ A := b0.2
  have hb0ne1' : (b0 : Q) ≠ 1 := fun h => hb0ne1 (Subtype.ext h)
  have hb0nea' : (b0 : Q) ≠ a := fun h => hb0nea (Subtype.ext h)
  have hb0sq : (b0 : Q) * b0 = 1 := by
    have h := hA2.2 (b0 : Q) b0.2
    simpa [pow_two] using h
  have hb0comm : a * b0 = b0 * a := by
    have h := isMulCommutative_iff.mp hA2.1 ⟨a, haA⟩ b0
    simpa using congrArg Subtype.val h
  have hb0inv : (b0 : Q)⁻¹ = b0 := inv_eq_of_mul_eq_one_right hb0sq
  have hb0notcent : (b0 : Q) ∉ centralizer (L : Set Q) := by
    intro h
    have hmem : (b0 : Q) ∈ A ⊓ centralizer (L : Set Q) := Subgroup.mem_inf.mpr ⟨hb0A, h⟩
    rw [hAL] at hmem
    exact hb0ne1' (Subgroup.mem_bot.mp hmem)
  refine ⟨hconj_comm a haL hainv, ?_⟩
  by_cases hb0N : (b0 : Q) ∈ normalizer (L : Set Q)
  · refine ⟨(b0 : Q), hb0A, hb0sq, hb0comm, Or.inl ⟨hb0N, ?_⟩⟩
    exact le_closure_commutator_of_mem_normalizer hL.2.2 hb0N hb0notcent
  · by_cases habN : a * b0 ∈ normalizer (L : Set Q)
    · have hb1 : (a * b0 : Q) ≠ 1 := by
        intro h
        have h2 : (b0 : Q) = a := by
          rw [eq_inv_of_mul_eq_one_right h, hainv]
        exact hb0nea' h2
      have hnotcent : (a * b0 : Q) ∉ centralizer (L : Set Q) := by
        intro hc
        have hmem : (a * b0 : Q) ∈ A ⊓ centralizer (L : Set Q) :=
          Subgroup.mem_inf.mpr ⟨A.mul_mem haA hb0A, hc⟩
        rw [hAL] at hmem
        exact hb1 (Subgroup.mem_bot.mp hmem)
      have hsq : (a * b0) * (a * b0) = 1 := by
        have h : (a * b0) * (a * b0) = (a * a) * (b0 * b0) := by
          calc (a * b0) * (a * b0) = a * (b0 * a) * b0 := by group
            _ = a * (a * b0) * b0 := by rw [← hb0comm]
            _ = (a * a) * (b0 * b0) := by group
        rw [h, haa, hb0sq, one_mul]
      have hcomm1 : a * (a * b0) = (a * b0) * a := by
        calc a * (a * b0) = (a * a) * b0 := by group
          _ = b0 := by rw [haa, one_mul]
          _ = (a * b0) * a := by rw [hb0comm, mul_assoc, haa, mul_one]
      refine ⟨a * b0, A.mul_mem haA hb0A, hsq, hcomm1, Or.inl ⟨habN, ?_⟩⟩
      exact le_closure_commutator_of_mem_normalizer hL.2.2 habN hnotcent
    · have hsq : (a * b0) * (a * b0) = 1 := by
        have h : (a * b0) * (a * b0) = (a * a) * (b0 * b0) := by
          calc (a * b0) * (a * b0) = a * (b0 * a) * b0 := by group
            _ = a * (a * b0) * b0 := by rw [← hb0comm]
            _ = (a * a) * (b0 * b0) := by group
        rw [h, haa, hb0sq, one_mul]
      have hinv : (a * b0)⁻¹ = a * b0 := inv_eq_of_mul_eq_one_right hsq
      exact ⟨(b0 : Q), hb0A, hb0sq, hb0comm,
        Or.inr ⟨hconj_comm (b0 : Q) hb0N hb0inv, hconj_comm (a * b0) habN hinv⟩⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
