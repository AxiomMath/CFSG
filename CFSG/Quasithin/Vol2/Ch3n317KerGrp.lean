module

public import CFSG.Quasithin.Vol2.Ch3n317A5

public section

open Equiv

namespace CFSG.Quasithin.Ch3n317Ker

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

section Count

omit [Finite G] in
theorem mem_centralizer_sup {X Y : Subgroup G} {x : G}
    (hX : x ∈ Subgroup.centralizer (X : Set G)) (hY : x ∈ Subgroup.centralizer (Y : Set G)) :
    x ∈ Subgroup.centralizer ((X ⊔ Y : Subgroup G) : Set G) := by
  have h1 : X ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hX)
  have h2 : Y ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hY)
  exact Subgroup.zpowers_le.mp (Subgroup.le_centralizer_iff.mpr (sup_le h1 h2))

theorem relIndex_eq_of_le_sup {W V C : Subgroup G} (hVW : V ≤ W) (hCW : C ≤ W)
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (h : W ≤ C ⊔ V) :
    C.relIndex W = (C ⊓ V).relIndex V := by
  have hn : C ≤ Subgroup.normalizer (V : Set G) := fun c hc =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      hW v (hVW hv) c (hCW hc))
  rw [B6.relIndex_inf_eq_relIndex_sup hn, le_antisymm (sup_le hCW hVW) h]

theorem le_sup_of_relIndex {W V X₁ X₂ : Subgroup G} (hVW : V ≤ W)
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (h₁ : W ≤ (W ⊓ Subgroup.centralizer (X₁ : Set G)) ⊔ V)
    (h₂ : W ≤ (W ⊓ Subgroup.centralizer (X₂ : Set G)) ⊔ V)
    (hc : (V ⊓ Subgroup.centralizer (X₁ : Set G)).relIndex V *
        (V ⊓ Subgroup.centralizer (X₂ : Set G)).relIndex V ≤
      (V ⊓ Subgroup.centralizer ((X₁ ⊔ X₂ : Subgroup G) : Set G)).relIndex V) :
    W ≤ (W ⊓ Subgroup.centralizer ((X₁ ⊔ X₂ : Subgroup G) : Set G)) ⊔ V := by
  set C₁ := W ⊓ Subgroup.centralizer (X₁ : Set G) with hC₁
  set C₂ := W ⊓ Subgroup.centralizer (X₂ : Set G) with hC₂
  set U := W ⊓ Subgroup.centralizer ((X₁ ⊔ X₂ : Subgroup G) : Set G) with hU
  have hUC : U = C₁ ⊓ C₂ := by
    ext x
    constructor
    · rintro ⟨hxW, hx⟩
      exact ⟨⟨hxW, Subgroup.centralizer_le (fun y hy => Subgroup.mem_sup_left hy) hx⟩,
        ⟨hxW, Subgroup.centralizer_le (fun y hy => Subgroup.mem_sup_right hy) hx⟩⟩
    · rintro ⟨⟨hxW, hx₁⟩, ⟨-, hx₂⟩⟩
      exact ⟨hxW, mem_centralizer_sup hx₁ hx₂⟩
  have hinf : ∀ X : Subgroup G, (W ⊓ Subgroup.centralizer (X : Set G)) ⊓ V =
      V ⊓ Subgroup.centralizer (X : Set G) := fun X => by
    rw [inf_right_comm, inf_eq_right.mpr hVW, inf_comm]
  have e₁ : C₁.relIndex W = (V ⊓ Subgroup.centralizer (X₁ : Set G)).relIndex V := by
    rw [relIndex_eq_of_le_sup hVW inf_le_left hW h₁, hinf]
  have e₂ : C₂.relIndex W = (V ⊓ Subgroup.centralizer (X₂ : Set G)).relIndex V := by
    rw [relIndex_eq_of_le_sup hVW inf_le_left hW h₂, hinf]
  have hUV : U ⊔ V ≤ W := sup_le inf_le_left hVW
  have eU : U.relIndex (U ⊔ V) =
      (V ⊓ Subgroup.centralizer ((X₁ ⊔ X₂ : Subgroup G) : Set G)).relIndex V := by
    have hW' : ∀ a ∈ U ⊔ V, ∀ b ∈ U ⊔ V, a * b = b * a := fun a ha b hb => hW a (hUV ha) b (hUV hb)
    rw [relIndex_eq_of_le_sup le_sup_right le_sup_left hW' le_rfl, hinf]
  have hmul := Subgroup.relIndex_mul_relIndex U (U ⊔ V) W le_sup_left hUV
  have hle : U.relIndex W ≤ C₁.relIndex W * C₂.relIndex W := by
    rw [hUC]
    exact Subgroup.relIndex_inf_le
  have hpos : U.relIndex (U ⊔ V) ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have h1 : U.relIndex (U ⊔ V) * (U ⊔ V).relIndex W ≤ U.relIndex (U ⊔ V) * 1 := by
    rw [hmul, mul_one]
    calc U.relIndex W ≤ C₁.relIndex W * C₂.relIndex W := hle
      _ ≤ _ := by rw [e₁, e₂, eU]; exact hc
  have h2 : (U ⊔ V).relIndex W ≤ 1 := Nat.le_of_mul_le_mul_left h1 (Nat.pos_of_ne_zero hpos)
  have h3 : (U ⊔ V).relIndex W = 1 :=
    le_antisymm h2 (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
  exact Subgroup.relIndex_eq_one.mp h3

end Count

omit [Finite G] in
theorem mem_centralizer_of_odd {V W : Subgroup G} (hV : IsElemAbelian 2 V) {z : G}
    (hz : Odd (orderOf z)) (hzV : z ∈ Subgroup.centralizer (V : Set G))
    (hzW : ∀ w ∈ W, w * z * w⁻¹ * z⁻¹ ∈ V) : z ∈ Subgroup.centralizer (W : Set G) := by
  have hz2 : z * z ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    set v := w * z * w⁻¹ * z⁻¹ with hv
    have hvV : v ∈ V := hzW w hw
    have hvz : z * v = v * z := (Subgroup.mem_centralizer_iff.mp hzV v hvV).symm
    have hvv : v * v = 1 := by
      have := hV.2 v hvV
      rwa [pow_two] at this
    have hwz : w * z = v * z * w := by rw [hv]; group
    calc w * (z * z) = (w * z) * z := by group
      _ = (v * z * w) * z := by rw [hwz]
      _ = v * z * (w * z) := by group
      _ = v * z * (v * z * w) := by rw [hwz]
      _ = v * (z * v) * z * w := by group
      _ = v * (v * z) * z * w := by rw [hvz]
      _ = (v * v) * (z * z) * w := by group
      _ = (z * z) * w := by rw [hvv, one_mul]
  obtain ⟨k, hk⟩ := hz
  have e : z = (z * z) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf z + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [e]
  exact Subgroup.pow_mem _ hz2 _

section Alpha

variable {V R : Subgroup G}

theorem alpha_facts (hV : IsElemAbelian 2 V) (hVR : V ≤ R)
    (hcard : ∀ A, IsMaxElemAbelian R A → ¬ A ≤ Subgroup.centralizer (V : Set G) →
      Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) :
    V ≤ omegaOneCenterOf (thompsonJ (R ⊓ Subgroup.centralizer (V : Set G))) ∧
    omegaOneCenterOf (thompsonJ R) ≤
      omegaOneCenterOf (thompsonJ (R ⊓ Subgroup.centralizer (V : Set G))) ∧
    (∀ A, IsMaxElemAbelian R A →
      omegaOneCenterOf (thompsonJ (R ⊓ Subgroup.centralizer (V : Set G))) ≤
        (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) := by
  set Q := R ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := B2F.le_centralizer_self hV
  have hVQ : V ≤ Q := le_inf hVR hVC
  have hsub : ∀ D, IsMaxElemAbelian Q D → IsMaxElemAbelian R D := by
    by_cases hex : ∃ A, IsMaxElemAbelian R A ∧ ¬ A ≤ Subgroup.centralizer (V : Set G)
    · obtain ⟨A, hA, hAC⟩ := hex
      exact (B24_three hV hVR hA (hcard A hA hAC)).2.2.1
    · push Not at hex
      obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian R
      have hA₀Q : A₀ ≤ Q := le_inf hA₀.1 (hex A₀ hA₀)
      intro D hD
      refine ⟨hD.1.trans inf_le_left, hD.2.1, fun B hBR hB => ?_⟩
      exact (hA₀.2.2 B hBR hB).trans (hD.2.2 A₀ hA₀Q hA₀.2.1)
  have hVD : ∀ D, IsMaxElemAbelian Q D → V ≤ D := by
    intro D hD
    have hDC : D ≤ Subgroup.centralizer (V : Set G) := hD.1.trans inf_le_right
    have hE : IsElemAbelian 2 (D ⊔ V) :=
      B2F.isElemAbelian_sup_of_commute hD.2.1 hV fun d hd v hv =>
        (Subgroup.mem_centralizer_iff.1 (hDC hd) v hv).symm
    have hEQ : D ⊔ V ≤ Q := sup_le hD.1 hVQ
    have h := Subgroup.eq_of_le_of_card_ge (le_sup_left : D ≤ D ⊔ V) (hD.2.2 _ hEQ hE)
    exact le_sup_right.trans (le_of_eq h.symm)
  have hE : ∀ A, IsMaxElemAbelian R A →
      IsMaxElemAbelian Q ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) := by
    intro A hA
    have hEe : IsElemAbelian 2 ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) :=
      B2F.isElemAbelian_sup_of_commute (B2F.isElemAbelian_mono inf_le_left hA.2.1) hV
        fun a ha v hv => (Subgroup.mem_centralizer_iff.1 ha.2 v hv).symm
    have hEQ : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V ≤ Q :=
      sup_le (le_inf (inf_le_left.trans hA.1) inf_le_right) hVQ
    refine ⟨hEQ, hEe, fun B hBQ hB => ?_⟩
    by_cases hAC : A ≤ Subgroup.centralizer (V : Set G)
    · have hAE : A ≤ (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V :=
        le_sup_of_le_left (le_inf le_rfl hAC)
      exact (hA.2.2 B (hBQ.trans inf_le_left) hB).trans (Subgroup.card_le_of_le hAE)
    · have hmax := (B24_three hV hVR hA (hcard A hA hAC)).1
      exact hmax.2.2 B (hBQ.trans inf_le_left) hB
  refine ⟨?_, ?_, fun A hA => ?_⟩
  · rw [(omegaOne_centralizer_thompsonJ Q).2]
    exact le_iInf₂ fun D hD => hVD D hD
  · rw [(omegaOne_centralizer_thompsonJ R).2, (omegaOne_centralizer_thompsonJ Q).2]
    exact le_iInf₂ fun D hD => iInf₂_le D (hsub D hD)
  · rw [(omegaOne_centralizer_thompsonJ Q).2]
    exact iInf₂_le _ (hE A hA)

end Alpha

omit [Finite G] in
theorem exists_pow_eq_mul {N : Subgroup G} {i t : G} (hi : i ∈ N)
    (ht : t ∈ Subgroup.normalizer (N : Set G)) : ∀ n : ℕ, ∃ j ∈ N, (i * t) ^ n = j * t ^ n := by
  intro n
  induction n with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨j, hj, hjn⟩ := ih
    have htn : t ^ n ∈ Subgroup.normalizer (N : Set G) := Subgroup.pow_mem _ ht n
    refine ⟨j * (t ^ n * i * (t ^ n)⁻¹), N.mul_mem hj
      ((Subgroup.mem_normalizer_iff.mp htn i).mp hi), ?_⟩
    rw [pow_succ, hjn, pow_succ]
    group

section Main

variable {H T M₂ V : Subgroup G}

theorem exists_mul_twoResidual (hmin : MinParabolic H T M₂) {h : G} (hh : h ∈ H) :
    ∃ k ∈ twoResidual H, ∃ t ∈ T, h = k * t := by
  have hsup := sup_twoResidual_eq hmin.isSylow
  rw [← hsup, sup_comm] at hh
  exact Ch3n317A5.exists_mul_of_mem_sup_of_le_normalizer
    (hmin.isSylow.1.trans (le_normalizer_twoResidual H)) hh

theorem pCoreOf_le_baum_of_facts (hmin : MinParabolic H T M₂) (hV : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hcard : ∀ A, IsMaxElemAbelian T A → ¬ A ≤ Subgroup.centralizer (V : Set G) →
      Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)))
    {k : G} (hk : k ∈ twoResidual H)
    (hgen : autI hV.2.2.1 (twoResidual H) ≤
      autI hV.2.2.1 (thompsonJ T ⊔ B6.conjSub k (thompsonJ T)))
    (hcount : (V ⊓ Subgroup.centralizer (thompsonJ T : Set G)).relIndex V *
        (V ⊓ Subgroup.centralizer (B6.conjSub k (thompsonJ T) : Set G)).relIndex V ≤
      (V ⊓ Subgroup.centralizer ((thompsonJ T ⊔ B6.conjSub k (thompsonJ T) : Subgroup G) :
        Set G)).relIndex V) :
    pCoreOf 2 (twoResidual H) ≤ baum T := by
  classical
  have hVe : IsElemAbelian 2 V := hV.2.2.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hV.2.1
  set K := twoResidual H with hKdef
  set J := thompsonJ T with hJdef
  set C := Subgroup.centralizer (V : Set G) with hCdef
  have hTH : T ≤ H := hmin.isSylow.1
  have hT2 : IsPGroup 2 T := hmin.isSylow.2.1
  have hKH : K ≤ H := twoResidual_le H
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTH.trans hHN
  have hHV : ¬ H ≤ C := fun h => hJ ((B6.thompsonJ_le T).trans (hTH.trans h))
  have hQ : T ⊓ C = pCoreOf 2 H := hmin.inf_centralizer_eq_pCoreOf hV hHV
  have hVT : V ≤ T :=
    (A4.le_pCoreOf_of_isTwoReducedIn hV).trans (pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow)
  have hJT : J ≤ T := B6.thompsonJ_le T
  have hJH : J ≤ H := hJT.trans hTH
  have hTJ : T ≤ Subgroup.normalizer (J : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  obtain ⟨hVα, hEα, hαA⟩ := alpha_facts hVe hVT hcard
  set α := omegaOneCenterOf (thompsonJ (T ⊓ C)) with hαdef
  set E := omegaOneCenterOf J with hEdef
  have hαe : IsElemAbelian 2 α := B2F.isElemAbelian_omegaOneCenterOf _
  have hHα : H ≤ Subgroup.normalizer (α : Set G) := by
    intro h hh
    have hhQ : h ∈ Subgroup.normalizer ((T ⊓ C : Subgroup G) : Set G) := by
      rw [hQ]
      exact le_normalizer_pCoreOf 2 H hh
    exact normalizer_le_normalizer_of_map_mulEquiv
      (F := fun X => omegaOneCenterOf (thompsonJ X))
      (fun φ X => by rw [omegaOneCenterOf_map_mulEquiv, thompsonJ_map_mulEquiv]) (T ⊓ C) hhQ
  have hαA' : ∀ A, IsMaxElemAbelian T A → ∀ x ∈ α, ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ V := by
    intro A hA x hx a ha
    obtain ⟨c, hc, v, hv, rfl⟩ := Ch3n317A5.exists_mul_of_mem_sup (A := A ⊓ C) (B := V)
      (fun c hc v hv => (Subgroup.mem_centralizer_iff.mp hc.2 v hv).symm) (hαA A hA hx)
    have hca : c * a = a * c := B2F.isElemAbelian_comm hA.2.1 hc.1 ha
    have haN : a ∈ Subgroup.normalizer (V : Set G) := hTN (hA.1 ha)
    have hy : v * (a * v⁻¹ * a⁻¹) ∈ V :=
      V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp haN _).mp (V.inv_mem hv))
    have hcy : c * (v * (a * v⁻¹ * a⁻¹)) = v * (a * v⁻¹ * a⁻¹) * c :=
      (Subgroup.mem_centralizer_iff.mp hc.2 _ hy).symm
    have hinv : c⁻¹ * a⁻¹ = a⁻¹ * c⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hca]
    have e : c * v * a * (c * v)⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) := by
      calc c * v * a * (c * v)⁻¹ * a⁻¹ = c * v * a * v⁻¹ * (c⁻¹ * a⁻¹) := by group
        _ = c * v * a * v⁻¹ * (a⁻¹ * c⁻¹) := by rw [hinv]
        _ = c * (v * (a * v⁻¹ * a⁻¹)) * c⁻¹ := by group
        _ = v * (a * v⁻¹ * a⁻¹) * c * c⁻¹ := by rw [hcy]
        _ = v * (a * v⁻¹ * a⁻¹) := by group
    rw [e]
    exact hy
  set I₀ := ⨆ h ∈ H, B6.conjSub h J with hI₀
  let P : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (V : Set G) ∧ ∀ x ∈ α, x * g * x⁻¹ * g⁻¹ ∈ V}
      one_mem' := ⟨Subgroup.one_mem _, fun x _ => by simp [V.one_mem]⟩
      mul_mem' := by
        rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
        refine ⟨Subgroup.mul_mem _ hgN hhN, fun x hx => ?_⟩
        have e : x * (g * h) * x⁻¹ * (g * h)⁻¹ =
            (x * g * x⁻¹ * g⁻¹) * (g * (x * h * x⁻¹ * h⁻¹) * g⁻¹) := by group
        rw [e]
        exact V.mul_mem (hg x hx) ((Subgroup.mem_normalizer_iff.mp hgN _).mp (hh x hx))
      inv_mem' := by
        rintro g ⟨hgN, hg⟩
        refine ⟨Subgroup.inv_mem _ hgN, fun x hx => ?_⟩
        have e : x * g⁻¹ * x⁻¹ * g⁻¹⁻¹ = g⁻¹ * (x * g * x⁻¹ * g⁻¹)⁻¹ * g⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) _).mp
          (V.inv_mem (hg x hx)) }
  have hJP : J ≤ P := by
    refine iSup₂_le fun A hA a ha => ⟨hTN (hA.1 ha), fun x hx => hαA' A hA x hx a ha⟩
  have hI₀P : I₀ ≤ P := by
    refine iSup₂_le fun h hh i hi => ?_
    have hj : h⁻¹ * i * h ∈ J := B6.mem_conjSub.mp hi
    have hjP := hJP hj
    have hhN : h ∈ Subgroup.normalizer (V : Set G) := hHN hh
    have e1 : i = h * (h⁻¹ * i * h) * h⁻¹ := by group
    refine ⟨?_, fun x hx => ?_⟩
    · rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hjP.1) (Subgroup.inv_mem _ hhN)
    · have hx' : h⁻¹ * x * h ∈ α := by
        have := (Subgroup.mem_normalizer_iff.mp (hHα (H.inv_mem hh)) x).mp hx
        simpa using this
      have h1 := hjP.2 _ hx'
      have e2 : x * i * x⁻¹ * i⁻¹ =
          h * ((h⁻¹ * x * h) * (h⁻¹ * i * h) * (h⁻¹ * x * h)⁻¹ * (h⁻¹ * i * h)⁻¹) * h⁻¹ := by
        group
      rw [e2]
      exact (Subgroup.mem_normalizer_iff.mp hhN _).mp h1
  have hαI₀ : ∀ x ∈ α, ∀ i ∈ I₀, x * i * x⁻¹ * i⁻¹ ∈ V := fun x hx i hi => (hI₀P hi).2 x hx
  have hJI₀ : ∀ h ∈ H, B6.conjSub h J ≤ I₀ := fun h hh =>
    le_iSup₂_of_le (f := fun h (_ : h ∈ H) => B6.conjSub h J) h hh le_rfl
  have hI₀H : I₀ ≤ H := iSup₂_le fun h hh i hi => by
    have hj : h⁻¹ * i * h ∈ J := B6.mem_conjSub.mp hi
    have e : i = h * (h⁻¹ * i * h) * h⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hh (hJH hj)) (H.inv_mem hh)
  have hHI₀ : H ≤ Subgroup.normalizer (I₀ : Set G) := by
    have key : ∀ g ∈ H, ∀ x ∈ I₀, g * x * g⁻¹ ∈ I₀ := by
      intro g hg x hx
      have hle : B6.conjSub g I₀ ≤ I₀ := by
        rw [hI₀, OrderIso.map_iSup₂]
        refine iSup₂_le fun h hh => ?_
        rw [← B6.conjSub_mul]
        exact hJI₀ _ (H.mul_mem hg hh)
      exact hle (B6.mem_conjSub.mpr (by simpa [mul_assoc] using hx))
    intro g hg
    exact B6.mem_normalizer_of_forall_mem (key g hg) fun x hx => by
      have := key g⁻¹ (H.inv_mem hg) x hx
      simpa using this
  have hsupH : I₀ ⊔ T = H := by
    by_contra hne
    have hlt : I₀ ⊔ T < H := lt_of_le_of_ne (sup_le hI₀H hTH) hne
    have hle := hmin.le_of_lt le_sup_right hlt
    have hker : I₀ ≤ kerIn M₂ H := fun x hx b hb =>
      hle (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hHI₀ hb) x).mp hx))
    have hJI : J ≤ I₀ := by
      have := hJI₀ 1 H.one_mem
      rwa [B6.conjSub_one] at this
    have hJO : J ≤ pCoreOf 2 H :=
      hmin.le_pCoreOf_of_isPGroup_of_le_kerIn (hT2.to_le hJT) (hJI.trans hker)
    exact hJ (hJO.trans (MinParabolic.pCoreOf_le_centralizer hV))
  have hKI₀ : K ≤ I₀ := by
    refine twoResidual_le_of_isTwoQuotient hI₀H hHI₀ fun y hy => ?_
    rw [← hsupH] at hy
    obtain ⟨i, hi, t, ht, rfl⟩ :=
      Ch3n317A5.exists_mul_of_mem_sup_of_le_normalizer (hTH.trans hHI₀) hy
    obtain ⟨n, hn⟩ := hT2 ⟨t, ht⟩
    have htn : t ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    obtain ⟨j, hj, hjn⟩ := exists_pow_eq_mul hi (hHI₀ (hTH ht)) (2 ^ n)
    refine ⟨n, ?_⟩
    rw [hjn, htn, mul_one]
    exact hj
  set Y := J ⊔ B6.conjSub k J with hYdef
  set W := E ⊔ V with hWdef
  have hWα : W ≤ α := sup_le hEα hVα
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hαe (hWα ha) (hWα hb)
  have hWI₀ : ∀ w ∈ W, ∀ i ∈ I₀, i * w * i⁻¹ ∈ W := by
    intro w hw i hi
    have hv := hαI₀ w (hWα hw) i hi
    have e : i * w * i⁻¹ = (w * i * w⁻¹ * i⁻¹)⁻¹ * w := by group
    rw [e]
    exact W.mul_mem (Subgroup.mem_sup_right (V.inv_mem hv)) hw
  have hkI₀ : k ∈ I₀ := hKI₀ hk
  have hkH : k ∈ H := hKH hk
  have hEJ : E ≤ Subgroup.centralizer (J : Set G) := by
    rw [hEdef, ← (omegaOne_centralizer_thompsonJ T).1]
    exact (B2F.omegaOneOf_le _).trans inf_le_right
  have h₁ : W ≤ (W ⊓ Subgroup.centralizer (J : Set G)) ⊔ V :=
    sup_le (le_sup_of_le_left (le_inf le_sup_left hEJ)) le_sup_right
  have h₂ : W ≤ (W ⊓ Subgroup.centralizer (B6.conjSub k J : Set G)) ⊔ V := by
    intro w hw
    have hw' : k⁻¹ * w * k⁻¹⁻¹ ∈ W := hWI₀ w hw _ (I₀.inv_mem hkI₀)
    obtain ⟨e, he, v, hv, hev⟩ := Ch3n317A5.exists_mul_of_mem_sup (A := E) (B := V)
      (fun a ha b hb => hWcomm a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb)) hw'
    have hw2 : w = (k * e * k⁻¹) * (k * v * k⁻¹) := by
      have : w = k * (k⁻¹ * w * k⁻¹⁻¹) * k⁻¹ := by group
      rw [this, hev]
      group
    rw [hw2]
    refine Subgroup.mul_mem_sup ⟨hWI₀ e (Subgroup.mem_sup_left he) k hkI₀,
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      ((Subgroup.mem_normalizer_iff.mp (hHN hkH) v).mp hv)
    have hy' : k⁻¹ * y * k ∈ J := B6.mem_conjSub.mp hy
    have h1 := Subgroup.mem_centralizer_iff.mp (hEJ he) _ hy'
    calc y * (k * e * k⁻¹) = k * ((k⁻¹ * y * k) * e) * k⁻¹ := by group
      _ = k * (e * (k⁻¹ * y * k)) * k⁻¹ := by rw [h1]
      _ = k * e * k⁻¹ * y := by group
  have hWY : W ≤ (W ⊓ Subgroup.centralizer (Y : Set G)) ⊔ V :=
    le_sup_of_relIndex le_sup_right hWcomm h₁ h₂ hcount
  set Z := Subgroup.closure {z | z ∈ K ⊓ C ∧ Odd (orderOf z)} with hZdef
  have hZW : Z ≤ Subgroup.centralizer (W : Set G) := by
    rw [hZdef, Subgroup.closure_le]
    rintro z ⟨⟨hzK, hzC⟩, hzo⟩
    exact mem_centralizer_of_odd hVe hzo hzC fun w hw => hαI₀ w (hWα hw) z (hKI₀ hzK)
  set Y₁ := Y ⊔ Z with hY₁def
  have hYH : Y ≤ H := sup_le hJH fun x hx => by
    have hj : k⁻¹ * x * k ∈ J := B6.mem_conjSub.mp hx
    have e : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hkH (hJH hj)) (H.inv_mem hkH)
  have hconjY₁ : ∀ y ∈ Y₁, B6.conjSub y J ≤ Y₁ := by
    intro y hy x hx
    have hj : y⁻¹ * x * y ∈ J := B6.mem_conjSub.mp hx
    have e : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
    rw [e]
    exact Y₁.mul_mem (Y₁.mul_mem hy (Subgroup.mem_sup_left (Subgroup.mem_sup_left hj)))
      (Y₁.inv_mem hy)
  have hK' : ∀ k' ∈ K, ∃ y ∈ Y₁, ∃ a ∈ T, k' = y * a := by
    intro k' hk'
    have hk'N : k' ∈ Subgroup.normalizer (V : Set G) := hHN (hKH hk')
    obtain ⟨y, hyY, hy⟩ := (mem_autI hVe).mp (hgen (convI_mem_autI hVe hk' hk'N))
    set c := (y : G)⁻¹ * k' with hc
    have hcC : c ∈ C := by
      have h1 : convI hVe (y⁻¹ * ⟨k', hk'N⟩) = 1 := by rw [map_mul, map_inv, hy, inv_mul_cancel]
      exact (convI_eq_one_iff hVe _).mp h1
    have hcH : c ∈ H := H.mul_mem (H.inv_mem (hYH hyY)) (hKH hk')
    obtain ⟨a, b, hcab, ha, hb, ⟨n, han⟩, hbo⟩ := B2F.exists_two_part_odd_part c
    have hzc : Subgroup.zpowers c ≤ H ⊓ C := Subgroup.zpowers_le.mpr ⟨hcH, hcC⟩
    have hbZ : b ∈ Z := by
      refine Subgroup.subset_closure ⟨⟨?_, (hzc hb).2⟩, hbo⟩
      exact F6.mem_twoResidual_of_odd (hzc hb).1 hbo
    have haT : a ∈ T := by
      have h1 : Subgroup.zpowers a ≤ kerIn M₂ H :=
        (Subgroup.zpowers_le.mpr (hzc ha)).trans (hmin.inf_centralizer_le_kerIn hV hHV)
      have h2 := hmin.le_pCoreOf_of_isPGroup_of_le_kerIn (B2F.isPGroup_zpowers han) h1
      exact pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow (h2 (Subgroup.mem_zpowers a))
    refine ⟨(y : G) * b, Y₁.mul_mem (Subgroup.mem_sup_left hyY) (Subgroup.mem_sup_right hbZ),
      a, haT, ?_⟩
    rw [mul_assoc, ← hcab, hc, mul_inv_cancel_left]
  have hI₀Y₁ : I₀ ≤ Y₁ := by
    refine iSup₂_le fun h hh => ?_
    obtain ⟨k', hk', t, ht, rfl⟩ := exists_mul_twoResidual hmin hh
    obtain ⟨y, hy, a, ha, rfl⟩ := hK' k' hk'
    rw [B6.conjSub_mul, B6.conjSub_mul, B6.conjSub_eq_self (hTJ ht),
      B6.conjSub_eq_self (hTJ ha)]
    exact hconjY₁ y hy
  have hKY₁ : K ≤ Y₁ := hKI₀.trans hI₀Y₁
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      ((le_normalizer_twoResidual H).trans (normalizer_le_normalizer_pCoreOf 2 K))
      (pCoreOf_isPGroup 2 K)
  intro o ho
  have hoT : o ∈ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow (hOK ho)
  have hoC : o ∈ C := MinParabolic.pCoreOf_le_centralizer hV (hOK ho)
  have hoY₁ : o ∈ Y₁ := hKY₁ (pCoreOf_le 2 K ho)
  refine ⟨hoT, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
  obtain ⟨u, hu, v, hv, rfl⟩ := Ch3n317A5.exists_mul_of_mem_sup
    (A := W ⊓ Subgroup.centralizer (Y : Set G)) (B := V)
    (fun a ha b hb => hWcomm a ha.1 b (Subgroup.mem_sup_right hb))
    (hWY (Subgroup.mem_sup_left he))
  have huo : o ∈ Subgroup.centralizer ({u} : Set G) := by
    have hY : Y ≤ Subgroup.centralizer ({u} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hu.2 y hy)
    have hZ : Z ≤ Subgroup.centralizer ({u} : Set G) := fun z hz =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hZW hz) u hu.1).symm
    exact sup_le hY hZ hoY₁
  have h1 : o * u = u * o := Subgroup.mem_centralizer_singleton_iff.mp huo
  have h2 : v * o = o * v := Subgroup.mem_centralizer_iff.mp hoC v hv
  calc u * v * o = u * (o * v) := by rw [mul_assoc, h2]
    _ = (u * o) * v := by group
    _ = o * (u * v) := by rw [← h1]; group

end Main

end CFSG.Quasithin.Ch3n317Ker
