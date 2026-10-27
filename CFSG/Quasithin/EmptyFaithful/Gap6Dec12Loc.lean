module

public import CFSG.Quasithin.EmptyFaithful.Gap6Dec12Y
public import CFSG.Quasithin.EmptyFaithful.S146R1
public import CFSG.Quasithin.EmptyFaithful.S146R4

public section

namespace CFSG.Quasithin

namespace Gap6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem exists_mem_not_mem_of_relIndex {T H H₀ Q : Subgroup G} (hT2 : IsPGroup 2 T)
    (hQT : Q ≤ T) (hQH₀ : Q ≤ H₀) (hH₀H : H₀ ≤ H) (h72 : Q.relIndex H = 72)
    (hind : H₀.relIndex H = 2) (h4 : 4 < Q.relIndex T) : ∃ t ∈ T, t ∉ H₀ := by
  by_contra hcon
  push Not at hcon
  have hTH₀ : T ≤ H₀ := fun t ht => hcon t ht
  have e1 := Subgroup.relIndex_mul_relIndex Q H₀ H hQH₀ hH₀H
  rw [hind, h72] at e1
  have e2 := Subgroup.relIndex_mul_relIndex Q T H₀ hQT hTH₀
  have h36 : Q.relIndex H₀ = 36 := by omega
  have hdvd36 : Q.relIndex T ∣ 36 := by
    rw [← h36, ← e2]
    exact dvd_mul_right _ _
  have hdvdT : Q.relIndex T ∣ Nat.card T := Subgroup.index_dvd_card (Q.subgroupOf T)
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  rw [hn] at hdvdT
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdT
  rw [ha] at h4 hdvd36
  have ha3 : 3 ≤ a := by
    by_contra hlt
    push Not at hlt
    interval_cases a <;> simp at h4
  have h8 : 8 ∣ 2 ^ a := by
    have : 2 ^ a = 8 * 2 ^ (a - 3) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
      congr 1
      omega
    rw [this]
    exact dvd_mul_right _ _
  have := h8.trans hdvd36
  omega

theorem exists_isDec12_of_isOFourPlusOn (S : Setting146 G T M) {H PQ : Subgroup G} {p : ℕ}
    (hred : IsRedCE T M H PQ p) (hp : p = 3) (hO : IsOFourPlusOn T M H) :
    ∃ H₀ H₁ H₂ : Subgroup G, ∃ t : G, IsDec12 T M H p H₀ H₁ H₂ t := by
  subst hp
  have hH : IsHTM T M H := hred.isHTM
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hUZ := S.conjClosure_le_normalizer_Z hH
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hUab := S.lemma_14_5_15_two hH
  have hQ : centralizerMod (quasithinOmegaOneCenter T) H (uK T M H) = pCoreOf 2 H := hO.2
  have hker : centralizerMod (quasithinOmegaOneCenter T) H ⁅conjClosure (VZ T M) H, H⁆ ≤
      centralizerMod (quasithinOmegaOneCenter T) H (conjClosure (VZ T M) H) := by
    have h1 : centralizerMod (quasithinOmegaOneCenter T) H ⁅conjClosure (VZ T M) H, H⁆ =
        pCoreOf 2 H := hQ
    rw [h1, S.lemma_14_5_15_four hH]
  have hc : Dec12Ctx (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) H :=
    ⟨hHN, hUZ, hHU, hUab, hker⟩
  obtain ⟨H₀, H₁, H₂, hd⟩ := hc.exists_data hO.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTH : T ≤ H := hH.1.1
  have hQT : pCoreOf 2 H ≤ T := S.pCoreOf_le_T hH
  have hQH₀ : pCoreOf 2 H ≤ H₀ := by
    rw [← hQ]
    exact hd.Q₁.trans hd.le₁
  obtain ⟨t, htT, htH₀⟩ := exists_mem_not_mem_of_relIndex hT2 hQT hQH₀ hd.le
    (S.relIndex_pCoreOf_of_isOFourPlusOn hH hO) hd.index
    (S.four_lt_relIndex_of_isOFourPlusOn hH hO)
  have hsw := hd.swap t (hTH htT) htH₀
  have hUQ : conjClosure (VZ T M) H ≤ pCoreOf 2 H := S.conjClosure_le_pCoreOf hH
  have hrank : ∀ Hi : Subgroup G, Hi ≤ H →
      (quasithinOmegaOneCenter T).relIndex (⁅conjClosure (VZ T M) H, Hi⁆ ⊔ quasithinOmegaOneCenter T) = 4 →
      mIdx (uHi T M H Hi) (quasithinOmegaOneCenter T) = 2 := by
    intro Hi hHi h4
    have hU₁ : uHi T M H Hi ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hHi
    have hp1 : IsPGroup 2 (uHi T M H Hi) := (pCoreOf_isPGroup 2 H).to_le (hU₁.trans hUQ)
    have h1 := HypF98.relIndex_eq_two_pow_mIdx (Y := quasithinOmegaOneCenter T) hp1
    have h2 : (quasithinOmegaOneCenter T).relIndex (uHi T M H Hi) = 4 := h4
    rw [h2] at h1
    exact Nat.pow_right_injective le_rfl (show 2 ^ mIdx (uHi T M H Hi) (quasithinOmegaOneCenter T) = 2 ^ 2 by
      rw [← h1])
  refine ⟨H₀, H₁, H₂, t, ?_⟩
  exact
    { le := hd.le
      index := hd.index
      Q₁ := by rw [← hQ]; exact hd.Q₁
      Q₂ := by rw [← hQ]; exact hd.Q₂
      le₁ := hd.le₁
      le₂ := hd.le₂
      sup := hd.sup
      inf := by rw [← hQ]; exact hd.inf
      comm := by rw [← hQ]; exact hd.comm
      dihedral₁ := by rw [← hQ]; exact hd.dihedral₁
      dihedral₂ := by rw [← hQ]; exact hd.dihedral₂
      t_mem := htT
      t_not := hsw.1
      conj := hsw.2
      dir_inf := hd.dir_inf
      dir_sup := hd.dir_sup
      cent₁ := hd.cent₁
      cent₂ := hd.cent₂
      rank₁ := ⟨fun h => absurd h (by norm_num), fun _ =>
        Or.inl (hrank H₁ (hd.le₁.trans hd.le) hd.card₁)⟩
      rank₂ := ⟨fun h => absurd h (by norm_num), fun _ =>
        Or.inl (hrank H₂ (hd.le₂.trans hd.le) hd.card₂)⟩ }

end Gap6

end CFSG.Quasithin
