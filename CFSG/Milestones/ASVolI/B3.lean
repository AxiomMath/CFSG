module

public import CFSG.Milestones.ASVolI.B1
public import CFSG.Quasithin.Background.B3ThreeMain
public import CFSG.Quasithin.Background.B3Four

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.B3 CFSG.ASVolI.ChB
open scoped commutatorElement

@[expose] def B_3_1 : Prop :=
  ∀ n : ℕ, SQTKn n →
    (Nontrivial (Mod.V n Mod.ut0) ∧
      ∀ X : Subgroup (Mod.V n Mod.ut0),
        (∀ g ∈ alternatingGroup (Fin n), ∀ v ∈ X, Mod.act n Mod.ut0 g v ∈ X) → X = ⊥ ∨ X = ⊤) ∧
    (n % 2 = 1 →
      U0 n ⊓ Esub n = ⊥ ∧ U0 n ⊔ Esub n = ⊤ ∧ rk (Mod.V n Mod.ut0) = n - 1 ∧
        ∃ φ : Mod.V n Mod.ut0 ≃* Mod.V n Mod.u0, ∀ (g : Gp n) (v : Mod.V n Mod.ut0),
          φ (Mod.act n Mod.ut0 g v) = Mod.act n Mod.u0 g (φ v)) ∧
    (n % 2 = 0 →
      (Esub n < U0 n ∧ U0 n < ⊤) ∧
      (∀ (g : Gp n), ∀ x ∈ Esub n, permAct n g x ∈ Esub n) ∧
      (∀ (g : Gp n), ∀ x ∈ U0 n, permAct n g x ∈ U0 n) ∧
      (∀ X : Subgroup (U n), (∀ g ∈ alternatingGroup (Fin n), ∀ x ∈ X, permAct n g x ∈ X) →
        X = ⊥ ∨ X = Esub n ∨ X = U0 n ∨ X = ⊤) ∧
      rk (Mod.V n Mod.ut0) = n - 2)

theorem as_B_3_1 : B_3_1 := by
  unfold B_3_1
  intro n hn
  have h5 : 5 ≤ n := hn.five_le
  exact ⟨CFSG.Quasithin.B3.B3_1_1 h5,
    fun hodd => CFSG.Quasithin.B3.B3_1_2 h5 hodd,
    fun hev => CFSG.Quasithin.B3.B3_1_3 h5 hev⟩

@[expose] def B_3_2 : Prop :=
  ∀ n : ℕ, SQTKn n → ∀ k : Mod,
    (∀ m : ℕ, 1 ≤ m → m ≤ n / 2 →
      rk (Am n m) = m ∧
      (¬ (CaseB n k ∧ m = n / 2) → rkIdx (fixV ((Am n m).map (Mod.act n k))) = m) ∧
      (CaseB n k ∧ m = n / 2 → rkIdx (fixV ((Am n m).map (Mod.act n k))) = n / 2 - 1)) ∧
    (CaseB n k → rk (A0 n) = n / 2 ∧ rkIdx (fixV ((A0 n).map (Mod.act n k))) = n / 2) ∧
    (n = 8 → k = Mod.ut0 → ∀ A ∈ Rset n, rkIdx (fixV (A.map (Mod.act n k))) = 3) ∧
    (CaseA n k →
      (∀ A : Subgroup (Gp n), IsOffG n k A ↔
        ∃ m, 1 ≤ m ∧ m ≤ n / 2 ∧ A ∈ conjClass (Am n m)) ∧
      (∃ T : Sylow 2 (Gp n), (∀ m, m ≤ n / 2 → Am n m ≤ T) ∧ A0 n ≤ T ∧
        ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) = (Dsub n).map (Mod.act n k)) ∧
      qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) = ((1 : ℚ) : WithTop ℚ)) ∧
    (CaseB n k → ¬ (n = 8 ∧ k = Mod.ut0) →
      (∀ A : Subgroup (Gp n), IsOffG n k A ↔
        A ∈ conjClass (Dsub n ⊓ alternatingGroup (Fin n)) ∨ A ∈ conjClass (A0 n) ∨
          (∃ m, 1 ≤ m ∧ m ≤ n / 2 ∧ A ∈ conjClass (Am n m)) ∨ A ∈ Hset n) ∧
      (∃ T : Sylow 2 (Gp n), (∀ m, m ≤ n / 2 → Am n m ≤ T) ∧ A0 n ≤ T ∧
        ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) =
          (Dsub n ⊔ Subgroup.closure
            {x : Gp n | x ∈ (T : Subgroup (Gp n)) ∧ IsConj (ti n 0 * ti n 1) x}).map
              (Mod.act n k)) ∧
      qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) = ((((n : ℚ) - 2) / n : ℚ) : WithTop ℚ)) ∧
    (n = 8 → k = Mod.ut0 →
      (∀ A : Subgroup (Gp n), IsOffG n k A ↔
        A ∈ conjClass (Dsub n ⊓ alternatingGroup (Fin n)) ∨ A ∈ conjClass (A0 n) ∨
          (∃ m, 1 ≤ m ∧ m ≤ 4 ∧ A ∈ conjClass (Am n m)) ∨ A ∈ Hset n ∨ A ∈ Rset n) ∧
      (∃ T : Sylow 2 (Gp n), (∀ m, m ≤ 4 → Am n m ≤ T) ∧ A0 n ≤ T ∧
        ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) = (T : Subgroup (Gp n)).map (Mod.act n k) ∧
        ∀ A : Subgroup (Gp n), A ≤ T →
          (IsStrongFFStarOffender ((T : Subgroup (Gp n)).map (Mod.act n k)) (A.map (Mod.act n k)) ↔
            A = Dsub n)) ∧
      qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) = ((3 / 4 : ℚ) : WithTop ℚ))

section

theorem as_B_3_2 : B_3_2 := by
  unfold B_3_2
  intro n hn k
  refine ⟨fun m hm1 hm2 => CFSG.Quasithin.B3.B3_2_1 hn k hm1 hm2,
    fun hB => CFSG.Quasithin.B3.B3_2_2 hn k hB, ?_,
    fun hA => CFSG.Quasithin.B3.B3_2_4 hn k hA,
    fun hB hexc => CFSG.Quasithin.B3.B3_2_5 hn k hB hexc, ?_⟩
  · intro h8 hk A hA
    subst h8 hk
    exact CFSG.Quasithin.B3.B3_2_3 hA
  · intro h8 hk
    subst h8 hk
    exact CFSG.Quasithin.B3.B3_2_6

end

@[expose] def B_3_3 : Prop :=
  ∀ n : ℕ, SQTKn n → ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    (∀ ρ : LG n →* MulAut V, HasOneChief n ρ → IsIndec ρ →
      (n % 2 = 1 →
        Nat.card (H1 (actL n Mod.ut0)) = 1 ∧
        (∃ Φ : V ≃* Mod.V n Mod.ut0, IsModIso ρ (actL n Mod.ut0) Φ) ∧
        (∃ Φ : Mod.V n Mod.ut0 ≃* Mod.V n Mod.u0, IsModIso (actL n Mod.ut0) (actL n Mod.u0) Φ) ∧
        (∃ Φ : Mod.V n Mod.ut0 ≃* Mod.V n Mod.ut, IsModIso (actL n Mod.ut0) (actL n Mod.ut) Φ)) ∧
      (n % 2 = 0 → Nat.card (H1 (actL n Mod.ut0)) = 2)) ∧
    (n % 2 = 0 → ∀ ρ : LG n →* MulAut V, HasOneChief n ρ → IsIndec ρ →
      (∃ θ : (V ⧸ fixG ρ) ≃* WV n, ∀ x v,
        θ (QuotientGroup.mk (ρ x v)) = actL n Mod.ut0 x (θ (QuotientGroup.mk v))) →
      (∃ Φ : V ≃* Mod.V n Mod.u0, IsModIso ρ (actL n Mod.u0) Φ) ∨
      (∃ Φ : V ≃* Mod.V n Mod.ut0, IsModIso ρ (actL n Mod.ut0) Φ)) ∧
    (n % 2 = 0 → ∀ ρG : Gp n →* MulAut V,
      HasOneChief n (ρG.comp (alternatingGroup (Fin n)).subtype) →
      IsIndec (ρG.comp (alternatingGroup (Fin n)).subtype) →
      (∃ θ : (V ⧸ fixG ρG) ≃* WV n, ∀ x v,
        θ (QuotientGroup.mk ((ρG.comp (alternatingGroup (Fin n)).subtype) x v)) =
          actL n Mod.ut0 x (θ (QuotientGroup.mk v))) →
      (∃ Φ : V ≃* Mod.V n Mod.u0,
        IsModIso (ρG.comp (alternatingGroup (Fin n)).subtype) (actL n Mod.u0) Φ) ∨
      (∃ Φ : V ≃* Mod.V n Mod.ut0,
        IsModIso (ρG.comp (alternatingGroup (Fin n)).subtype) (actL n Mod.ut0) Φ)) ∧
    (n % 2 = 0 → ∀ ρ : LG n →* MulAut V, HasOneChief n ρ → IsIndec ρ →
      ((∃ φ : ↥(commG ρ) ≃* WV n,
          IsModIso (resAct ρ (commG ρ) (isInv_commG ρ)) (actL n Mod.ut0) φ) →
        (∃ Φ : V ≃* Mod.V n Mod.ut, IsModIso ρ (actL n Mod.ut) Φ) ∨
        (∃ Φ : V ≃* Mod.V n Mod.ut0, IsModIso ρ (actL n Mod.ut0) Φ)) ∧
      ((∃ Φ : V ≃* Mod.V n Mod.u, IsModIso ρ (actL n Mod.u) Φ) ∨
        (∃ Φ : V ≃* Mod.V n Mod.u0, IsModIso ρ (actL n Mod.u0) Φ) ∨
        (∃ Φ : V ≃* Mod.V n Mod.ut, IsModIso ρ (actL n Mod.ut) Φ) ∨
        (∃ Φ : V ≃* Mod.V n Mod.ut0, IsModIso ρ (actL n Mod.ut0) Φ)))

theorem as_B_3_3 : B_3_3 := by
  unfold B_3_3
  intro n hn V _ _ hV
  have hodd : n % 2 = 1 → n = 5 ∨ n = 7 := by
    intro h
    rcases hn with rfl | rfl | rfl | rfl <;> omega
  have heven : n % 2 = 0 → n = 6 ∨ n = 8 := by
    intro h
    rcases hn with rfl | rfl | rfl | rfl <;> omega
  refine ⟨fun ρ hone hindec => ⟨fun h1 => CFSG.Quasithin.B3.B3_3_1_odd (hodd h1) hV hone hindec,
      fun h0 => CFSG.Quasithin.B3.B3_3_1_even (heven h0)⟩,
    fun h0 ρ hone hindec hquot => CFSG.Quasithin.B3.B3_3_2_L (heven h0) hV hone hindec hquot,
    fun h0 ρG hone hindec hquot =>
      CFSG.Quasithin.B3.B3_3_2_G ρG (heven h0) hV hone hindec hquot,
    fun h0 ρ hone hindec => ⟨fun hcomm => CFSG.Quasithin.B3.B3_3_3 (heven h0) hV hone hindec hcomm,
      CFSG.Quasithin.B3.B3_3_4 (heven h0) hV hone hindec⟩⟩

@[expose] def B_3_4 : Prop :=
  ∀ k : Mod, (k = Mod.u0 ∨ k = Mod.ut0) →
    (∀ P : Set (Subgroup (MulAut (Mod.V 6 k))),
      IsStableFF ((alternatingGroup (Fin 6)).map (Mod.act 6 k)) P →
      ∀ T : Subgroup (Gp 6), IsSylow2In (alternatingGroup (Fin 6)) T →
      ∀ W₁ W₂ : Subgroup (Mod.V 6 k),
        IsFlagSpace 6 k (alternatingGroup (Fin 6)) T 1 W₁ →
        IsFlagSpace 6 k (alternatingGroup (Fin 6)) T 2 W₂ →
      ∀ H₁ H₂ R₁ R₂ : Subgroup (Gp 6),
        H₁ = stabW (alternatingGroup (Fin 6)) W₁ → H₂ = stabW (alternatingGroup (Fin 6)) W₂ →
        R₁ = O2s H₁ → R₂ = O2s H₂ →
      ∀ J J₁ : Subgroup (MulAut (Mod.V 6 k)),
        J = ffJP P (T.map (Mod.act 6 k)) → J₁ = ffJP P (R₁.map (Mod.act 6 k)) →
          J = R₂.map (Mod.act 6 k) ∧ rk R₂ = 2 ∧
          (∀ A : Subgroup (MulAut (Mod.V 6 k)), A ≤ R₂.map (Mod.act 6 k) →
            ¬ IsStrongFFStarOffender ((alternatingGroup (Fin 6)).map (Mod.act 6 k)) A) ∧
          J₁ = ⊥) ∧
    (∀ P : Set (Subgroup (MulAut (Mod.V 6 k))),
      IsStableFF ((⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)) P →
      ∀ T : Subgroup (Gp 6), IsSylow2In ⊤ T →
      ∀ W₁ W₂ : Subgroup (Mod.V 6 k), IsFlagSpace 6 k ⊤ T 1 W₁ → IsFlagSpace 6 k ⊤ T 2 W₂ →
      ∀ H₁ H₂ R₁ R₂ L₁ L₂ : Subgroup (Gp 6),
        H₁ = stabW ⊤ W₁ → H₂ = stabW ⊤ W₂ → R₁ = O2s H₁ → R₂ = O2s H₂ →
        L₁ = H₁ ⊓ alternatingGroup (Fin 6) → L₂ = H₂ ⊓ alternatingGroup (Fin 6) →
      ∀ J J₁ : Subgroup (MulAut (Mod.V 6 k)),
        J = ffJP P (T.map (Mod.act 6 k)) → J₁ = ffJP P (R₁.map (Mod.act 6 k)) →
          FourG k P T R₁ R₂ L₁ L₂ J J₁)

section

theorem as_B_3_4 : B_3_4 := by
  unfold B_3_4
  intro k hk
  refine ⟨fun P hP T hT W₁ W₂ hW₁ hW₂ H₁ H₂ R₁ R₂ hH₁ hH₂ hR₁ hR₂ J J₁ hJ hJ₁ =>
      CFSG.Quasithin.B3.B3_4_1 hk hP hT hW₁ hW₂ hH₁ hH₂ hR₁ hR₂ hJ hJ₁,
    fun P hP T hT W₁ W₂ hW₁ hW₂ H₁ H₂ R₁ R₂ L₁ L₂ hH₁ hH₂ hR₁ hR₂ hL₁ hL₂ J J₁ hJ hJ₁ =>
      CFSG.Quasithin.B3.B3_4_2 hk hP hT hW₁ hW₂ hH₁ hH₂ hR₁ hR₂ hL₁ hL₂ hJ hJ₁⟩

end

end CFSG.ASVolI
