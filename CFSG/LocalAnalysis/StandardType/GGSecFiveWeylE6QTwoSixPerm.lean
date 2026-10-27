module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCover
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoInnerQ
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixPermAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixPermAux2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixPermAux7

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem mem_zpowers_of_forall_conj_of_card_six
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hLx : L ≤ Subgroup.centralizer {x}) {b : G} (hb : b ∈ Bs)
    (hfix : ∀ l ∈ L, l ∈ Subgroup.normalizer (Bs : Set G) →
      l * b * l⁻¹ * b⁻¹ ∈ Subgroup.zpowers x) :
    b ∈ Subgroup.zpowers x := by
  classical
  obtain ⟨-, hrange5, Q, hQ, hfull⟩ :=
    e6QTwoSixFrameFullDiagonal hK θ hperf hBs hcard hx hBL hNL hI
  have hb' : b ∈ Bs := hb
  obtain ⟨σ, hσ0, hσ3, hσfr⟩ :=
    e6QTwoSixFrameAct_of_mem_range hK hNL θ hfull hrange5
      (MonoidHom.mem_range.mpr ⟨⟨b, hb'⟩, rfl⟩)
  have hswap : ∀ i j : Fin 6, i ≠ j → σ i = σ j := by
    intro i j hij
    obtain ⟨n', hnL, hnN, b₀, hact⟩ :=
      e6QTwoSix_exists_mem_normalizer hK θ hNL hfull hrange5 hperf hBs hcard hx hx1 hBL
        hstar hI hLx (Equiv.swap i j)
    have hfixn : n' * (b : G) * n'⁻¹ * (b : G)⁻¹ ∈ Subgroup.zpowers x := hfix n' hnL hnN
    have hmemBs : n' * (b : G) * n'⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hnN (b : G)).mp hb'
    have hmemBs' : n' * (b : G) * n'⁻¹ * (b : G)⁻¹ ∈ Bs :=
      Bs.mul_mem hmemBs (Bs.inv_mem hb')
    have hβ1 : e6QTwoSixFrameAction hNL θ
        ⟨n' * (b : G) * n'⁻¹ * (b : G)⁻¹, hmemBs'⟩ = 1 :=
      (e6QTwoSixFrameAction_eq_one_iff θ hNL hperf hBL
        ⟨n' * (b : G) * n'⁻¹ * (b : G)⁻¹, hmemBs'⟩).mpr hfixn
    have hβne : e6QTwoSixFrameAction hNL θ ⟨n' * (b : G) * n'⁻¹, hmemBs⟩ =
        e6QTwoSixFrameAction hNL θ ⟨b, hb'⟩ := by
      have h1 : e6QTwoSixFrameAction hNL θ
          ⟨n' * (b : G) * n'⁻¹ * (b : G)⁻¹, hmemBs'⟩ =
          e6QTwoSixFrameAction hNL θ ⟨n' * (b : G) * n'⁻¹, hmemBs⟩ *
            (e6QTwoSixFrameAction hNL θ ⟨b, hb'⟩)⁻¹ := by
        have heq : (⟨n' * (b : G) * n'⁻¹ * (b : G)⁻¹, hmemBs'⟩ : ↥Bs) =
            ⟨n' * (b : G) * n'⁻¹, hmemBs⟩ * ⟨b, hb'⟩⁻¹ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [heq, map_mul, map_inv]
      rw [h1] at hβ1
      simpa using (mul_inv_eq_one.mp hβ1)
    have hAeq : e6QTwoSixConjOnQuot θ ⟨n', hnL⟩ *
        e6QTwoSixFrameAction hNL θ ⟨b, hb'⟩ *
        (e6QTwoSixConjOnQuot θ ⟨n', hnL⟩)⁻¹ =
        e6QTwoSixFrameAction hNL θ ⟨b, hb'⟩ := by
      have hconj := e6QTwoSixFrameAction_conj θ hNL hnL (b := ⟨b, hb'⟩) hmemBs
      rw [← hconj]
      exact hβne
    rw [show e6QTwoSixConjOnQuot θ ⟨n', hnL⟩ =
        e6QTwoSixNormAction θ ⟨n', Subgroup.le_normalizer hnL⟩ from
      (e6QTwoSixNormAction_of_mem_L θ ⟨n', hnL⟩).symm, hact] at hAeq
    obtain ⟨σ₀, hσ₀0, hσ₀3, hσ₀fr⟩ :=
      e6QTwoSixFrameAct_of_mem_range hK hNL θ hfull hrange5
        (MonoidHom.mem_range.mpr ⟨b₀, rfl⟩)
    have hbb : e6QTwoSixFrameAction hNL θ b₀ * e6QTwoSixFrameAction hNL θ ⟨b, hb'⟩ =
        e6QTwoSixFrameAction hNL θ ⟨b, hb'⟩ * e6QTwoSixFrameAction hNL θ b₀ :=
      e6QTwoSix_frameAct_comm hK hσ₀3 hσ3 hσ₀fr hσfr
    have hw : e6QTwoSixFramePerm hK hQ (Equiv.swap i j) *
        e6QTwoSixFrameAction hNL θ ⟨b, hb'⟩ *
        (e6QTwoSixFramePerm hK hQ (Equiv.swap i j))⁻¹ =
        e6QTwoSixFrameAction hNL θ ⟨b, hb'⟩ := by
      set a := e6QTwoSixFrameAction hNL θ b₀
      set w := e6QTwoSixFramePerm hK hQ (Equiv.swap i j)
      set y := e6QTwoSixFrameAction hNL θ ⟨b, hb'⟩
      have hax : a * y * a⁻¹ = y := by
        rw [show a * y = y * a from hbb, mul_assoc, mul_inv_cancel, mul_one]
      have haxinv : a⁻¹ * y * a = y := by
        have h := congrArg (fun z => a⁻¹ * z * a) hax
        rw [show a⁻¹ * (a * y * a⁻¹) * a = y from by group] at h
        exact h.symm
      have hconj : a⁻¹ * ((a * w * a⁻¹) * y * (a * w * a⁻¹)⁻¹) * a =
          a⁻¹ * y * a := congrArg (fun z => a⁻¹ * z * a) hAeq
      have hleft : a⁻¹ * ((a * w * a⁻¹) * y * (a * w * a⁻¹)⁻¹) * a =
          w * (a⁻¹ * y * a) * w⁻¹ := by group
      rw [hleft, haxinv] at hconj
      exact hconj
    exact e6QTwoSixFrameAct_apply_eq_of_swap hK hσ3 hσfr hij hw
  have hσconst : ∀ i : Fin 6, σ i = σ (0 : Fin 6) := by
    intro i
    by_cases hi : i = 0
    · rw [hi]
    · exact hswap i 0 hi
  have hσ_one : σ = fun _ => (1 : Kˣ) := by
    funext i
    rw [hσconst i, hσ0]
  have hβ_one : e6QTwoSixFrameAction hNL θ ⟨b, hb'⟩ = 1 := by
    have h1 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (1 : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))
        (fun _ => (1 : Kˣ)) := TableBUD.frameAct_one
    have h2 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ ⟨b, hb'⟩) (fun _ => (1 : Kˣ)) := by
      rw [← hσ_one]; exact hσfr
    exact TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour hK) (Q := Q) (hQ := hQ)
      (hσ := fun _ => by norm_num) h2 h1
  exact (e6QTwoSixFrameAction_eq_one_iff θ hNL hperf hBL ⟨b, hb'⟩).mp hβ_one

theorem le_card_ggAutomizer_of_card_six
    (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hLx : L ≤ Subgroup.centralizer {x}) :
    720 ≤ Nat.card (ggAutomizer L Bs) := by
  classical
  obtain ⟨-, hrange5, Q, hQ, hfull⟩ :=
    e6QTwoSixFrameFullDiagonal hK θ hperf hBs hcard hx hBL hNL hI
  have hfull' : ∀ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
        TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ :=
    fun σ h1 h3 => by
      obtain ⟨b, hb⟩ := hfull σ h1 h3
      exact ⟨e6QTwoSixFrameAction hNL θ b, hb⟩
  have hex : ∀ τ : Equiv.Perm (Fin 6), ∃ n' : G, n' ∈ L ∧
      ∃ hn' : n' ∈ Subgroup.normalizer (Bs : Set G),
        ∀ (b : ↥Bs) (σ : Fin 6 → Kˣ), (∀ k, σ k ^ 3 = 1) →
          TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
            (e6QTwoSixFrameAction hNL θ b) σ →
          TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
            (e6QTwoSixFrameAction hNL θ
              ⟨n' * (b : G) * n'⁻¹,
                (Subgroup.mem_normalizer_iff.mp hn' (b : G)).mp b.2⟩) (σ ∘ ⇑τ.symm) :=
    fun τ => exists_mem_normalizer_frameAct_perm hK θ hNL hfull hrange5 hperf hBs hcard
      hx hx1 hBL hstar hI hLx τ
  let nτ : Equiv.Perm (Fin 6) → G := fun τ => Classical.choose (hex τ)
  have hnτL : ∀ τ, nτ τ ∈ L := fun τ =>
    (Classical.choose_spec (hex τ)).1
  have hnτN : ∀ τ, nτ τ ∈ Subgroup.normalizer (Bs : Set G) := fun τ =>
    (Classical.choose_spec (hex τ)).2.1
  have hnτfr : ∀ (τ : Equiv.Perm (Fin 6)) (b : ↥Bs) (σ : Fin 6 → Kˣ),
      (∀ k, σ k ^ 3 = 1) →
      TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ b) σ →
      TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ
          ⟨nτ τ * (b : G) * (nτ τ)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hnτN τ) (b : G)).mp b.2⟩) (σ ∘ ⇑τ.symm) :=
    fun τ => (Classical.choose_spec (hex τ)).2.2
  let φ : Equiv.Perm (Fin 6) → MulAut ↥Bs := fun τ =>
    Subgroup.normalizerMonoidHom Bs ⟨nτ τ, hnτN τ⟩
  have hφmem : ∀ τ, φ τ ∈ ggAutomizer L Bs := by
    intro τ
    apply Subgroup.subset_closure
    refine ⟨nτ τ, hnτL τ, hnτN τ, fun b => ?_⟩
    exact Subgroup.normalizerMonoidHom_apply_apply_coe Bs ⟨nτ τ, hnτN τ⟩ b
  have hφinj : Function.Injective φ := by
    intro τ τ' hφ
    apply e6QTwoSixFramePerm_injective_of_forall hK hfull'
    intro σ hσ3 e he
    let σ₀ : Fin 6 → Kˣ := fun k => (σ (0 : Fin 6))⁻¹ * σ k
    have hσ₀0 : σ₀ (0 : Fin 6) = 1 := by
      show (σ 0)⁻¹ * σ 0 = 1
      exact inv_mul_cancel _
    have hσ₀3 : ∀ k, σ₀ k ^ 3 = 1 := by
      intro k
      show ((σ 0)⁻¹ * σ k) ^ 3 = 1
      rw [mul_pow, inv_pow, hσ3 (0 : Fin 6), hσ3 k, inv_one, one_mul]
    have he₀ : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ₀ := by
      have := TableBUD.FrameAct.smul he (σ (0 : Fin 6))⁻¹
      simpa [σ₀, mul_comm] using this
    have herange := e6QTwoSixFrameAct_mem_range hK hNL θ hfull hσ₀0 hσ₀3 he₀
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp herange
    have hb' : e6QTwoSixFrameAction hNL θ b = e := hb
    have hnb : nτ τ * (b : G) * (nτ τ)⁻¹ = nτ τ' * (b : G) * (nτ τ')⁻¹ := by
      have h := congrArg (fun ψ : MulAut ↥Bs => (ψ b : G)) hφ
      simpa only [φ, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
    have hnbB : nτ τ * (b : G) * (nτ τ)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp (hnτN τ) (b : G)).mp b.2
    have hnbB' : nτ τ' * (b : G) * (nτ τ')⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp (hnτN τ') (b : G)).mp b.2
    have hconjτ := e6QTwoSixFrameAction_conj θ hNL (hnτL τ) (b := b) hnbB
    have hconjτ' := e6QTwoSixFrameAction_conj θ hNL (hnτL τ') (b := b) hnbB'
    have hAτ : e6QTwoSixFrameAction hNL θ ⟨nτ τ * (b : G) * (nτ τ)⁻¹, hnbB⟩ =
        e6QTwoSixConjOnQuot θ ⟨nτ τ, hnτL τ⟩ * e6QTwoSixFrameAction hNL θ b *
          (e6QTwoSixConjOnQuot θ ⟨nτ τ, hnτL τ⟩)⁻¹ := hconjτ
    have hAτ' : e6QTwoSixFrameAction hNL θ ⟨nτ τ' * (b : G) * (nτ τ')⁻¹, hnbB'⟩ =
        e6QTwoSixConjOnQuot θ ⟨nτ τ', hnτL τ'⟩ * e6QTwoSixFrameAction hNL θ b *
          (e6QTwoSixConjOnQuot θ ⟨nτ τ', hnτL τ'⟩)⁻¹ := hconjτ'
    rw [hb'] at hAτ hAτ'
    have hsame : e6QTwoSixConjOnQuot θ ⟨nτ τ, hnτL τ⟩ *
          e *
          (e6QTwoSixConjOnQuot θ ⟨nτ τ, hnτL τ⟩)⁻¹ =
        e6QTwoSixConjOnQuot θ ⟨nτ τ', hnτL τ'⟩ *
          e *
          (e6QTwoSixConjOnQuot θ ⟨nτ τ', hnτL τ'⟩)⁻¹ := by
      rw [← hAτ, ← hAτ']
      exact congrArg (fun x : ↥Bs => e6QTwoSixFrameAction hNL θ x)
        (Subtype.ext hnb)
    have hbβ : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ b) σ₀ := by
      rw [hb']; exact he₀
    have hwτ : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFramePerm hK hQ τ * e * (e6QTwoSixFramePerm hK hQ τ)⁻¹)
        (σ₀ ∘ ⇑τ.symm) := by
      rw [← hb']
      exact e6QTwoSixFrameAct_perm hK hbβ τ
    have hwτ' : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFramePerm hK hQ τ' * e * (e6QTwoSixFramePerm hK hQ τ')⁻¹)
        (σ₀ ∘ ⇑τ'.symm) := by
      rw [← hb']
      exact e6QTwoSixFrameAct_perm hK hbβ τ'
    have hσ₀τ3 : ∀ k, (σ₀ ∘ ⇑τ.symm) k ^ 3 = 1 := fun k => hσ₀3 _
    have hσ₀τ'3 : ∀ k, (σ₀ ∘ ⇑τ'.symm) k ^ 3 = 1 := fun k => hσ₀3 _
    have hAτfr : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixConjOnQuot θ ⟨nτ τ, hnτL τ⟩ * e *
          (e6QTwoSixConjOnQuot θ ⟨nτ τ, hnτL τ⟩)⁻¹) (σ₀ ∘ ⇑τ.symm) := by
      have h := hnτfr τ b σ₀ hσ₀3 (by rw [hb']; exact he₀)
      rwa [hAτ] at h
    have hAτ'fr : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixConjOnQuot θ ⟨nτ τ', hnτL τ'⟩ * e *
          (e6QTwoSixConjOnQuot θ ⟨nτ τ', hnτL τ'⟩)⁻¹) (σ₀ ∘ ⇑τ'.symm) := by
      have h := hnτfr τ' b σ₀ hσ₀3 (by rw [hb']; exact he₀)
      rwa [hAτ'] at h
    have huniq : e6QTwoSixConjOnQuot θ ⟨nτ τ, hnτL τ⟩ * e *
        (e6QTwoSixConjOnQuot θ ⟨nτ τ, hnτL τ⟩)⁻¹ =
        e6QTwoSixFramePerm hK hQ τ * e * (e6QTwoSixFramePerm hK hQ τ)⁻¹ :=
      TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour hK) (Q := Q) (hQ := hQ)
        (hσ := fun k => e6QTwoSixPowThreeVal hK hσ₀τ3 k) hAτfr hwτ
    have huniq' : e6QTwoSixConjOnQuot θ ⟨nτ τ', hnτL τ'⟩ * e *
        (e6QTwoSixConjOnQuot θ ⟨nτ τ', hnτL τ'⟩)⁻¹ =
        e6QTwoSixFramePerm hK hQ τ' * e * (e6QTwoSixFramePerm hK hQ τ')⁻¹ :=
      TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour hK) (Q := Q) (hQ := hQ)
        (hσ := fun k => e6QTwoSixPowThreeVal hK hσ₀τ'3 k) hAτ'fr hwτ'
    rw [← huniq, ← huniq']
    exact hsame
  have hcardPerm : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  calc 720 = Nat.card (Equiv.Perm (Fin 6)) := hcardPerm.symm
    _ ≤ Nat.card ↥(ggAutomizer L Bs) :=
        Nat.card_le_card_of_injective (fun τ => (⟨φ τ, hφmem τ⟩ : ↥(ggAutomizer L Bs)))
          (fun τ τ' h => hφinj (Subtype.ext_iff.mp h))
    _ = Nat.card (ggAutomizer L Bs) := rfl

end CFSG.StandardType.E6QTwo

end
