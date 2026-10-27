module

public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.D2Tools
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped Pointwise

section Elementary

variable {G : Type} [Group G]

theorem isElemAbelian_zpowers151b {x : G} (hx : x ^ 2 = 1) :
    IsElemAbelian 2 (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem card_sup_mul_card_inf_of_commute151b [Finite G] (L R : Subgroup G)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup G) * Nat.card (L ⊓ R : Subgroup G) = Nat.card L * Nat.card R ∧
    ((L ⊔ R : Subgroup G) : Set G) = (L : Set G) * (R : Set G) := by
  let μ : L × R →* G := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : G) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hset : ((L ⊔ R : Subgroup G) : Set G) = (L : Set G) * (R : Set G) := by
    rw [← hrange]
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.1.2, x.2, x.2.2, rfl⟩
    · rintro ⟨l, hl, r, hr, rfl⟩
      exact ⟨(⟨l, hl⟩, ⟨r, hr⟩), rfl⟩
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : G)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  exact ⟨by rw [mul_comm]; exact this, hset⟩

theorem isElemAbelian_sup_of_commute151b [Finite G] {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hc

end Elementary

section Counting

variable {G : Type} [Group G] [Finite G]

theorem card_le_two_pow_pRank151b {E H : Subgroup G} (hEH : E ≤ H) (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ 2 ^ CFSG.Open.pRank 2 H := by
  have hp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have := le_pRank Nat.prime_two hEH hE hk
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) this

theorem inf_centralizer_le_of_corank_one151b {T V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVT : V ≤ T) (hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hA : IsElemAbelianCorank T 1 A) (hA1 : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    V ⊓ Subgroup.centralizer (A : Set G) ≤ A := by
  intro v hv
  by_contra hvA
  have hvV : v ∈ V := hv.1
  have hv2 : v ^ 2 = 1 := hV.2 v hvV
  have hcomm : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers v, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := hb
    have h1 : Commute a v := Subgroup.mem_centralizer_iff.mp hv.2 a ha
    exact (h1.zpow_right m).eq
  have hBE : IsElemAbelian 2 (A ⊔ Subgroup.zpowers v) :=
    isElemAbelian_sup_of_commute151b hA.2.1 (isElemAbelian_zpowers151b hv2) hcomm
  have hBT : A ⊔ Subgroup.zpowers v ≤ T :=
    sup_le hA.1 (Subgroup.zpowers_le.mpr (hVT hvV))
  have hAB : A ≤ A ⊔ Subgroup.zpowers v := le_sup_left
  have hlt : Nat.card A < Nat.card (A ⊔ Subgroup.zpowers v : Subgroup G) := by
    by_contra hge
    push Not at hge
    have heq : A = A ⊔ Subgroup.zpowers v := Subgroup.eq_of_le_of_card_ge hAB hge
    exact hvA (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hAB
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hcard := hA.2.2
  have hle := card_le_two_pow_pRank151b hBT hBE
  have hc2 : c = 2 := by
    have h1 : Nat.card A * c ≤ Nat.card A * 2 := by
      rw [← hc]
      calc Nat.card (A ⊔ Subgroup.zpowers v : Subgroup G) ≤ 2 ^ CFSG.Open.pRank 2 T := hle
        _ = Nat.card A * 2 := by rw [← hcard]; ring
    have h2 : Nat.card A * 1 < Nat.card A * c := by
      rw [← hc]
      simpa using hlt
    have h3 := Nat.le_of_mul_le_mul_left h1 hApos
    have h4 := Nat.lt_of_mul_lt_mul_left h2
    omega
  have hBcard : Nat.card (A ⊔ Subgroup.zpowers v : Subgroup G) * 2 ^ 0 = 2 ^ CFSG.Open.pRank 2 T := by
    rw [hc, hc2, ← hcard]
    ring
  have hBmax : IsMaxElemAbelian T (A ⊔ Subgroup.zpowers v) :=
    isMaxElemAbelian_iff_corank_zero.mpr ⟨hBT, hBE, hBcard⟩
  have hBJ : A ⊔ Subgroup.zpowers v ≤ thompsonJ T := le_iSup₂_of_le _ hBmax le_rfl
  exact hA1 (hAB.trans (hBJ.trans hJ))

theorem card_mul_le_of_corank_one151b {T V A : Subgroup G} (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hA : IsElemAbelianCorank T 1 A) :
    Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) ≤
      2 * Nat.card A * Nat.card (V ⊓ A : Subgroup G) := by
  set C : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G) with hC
  have hcomm : ∀ c ∈ C, ∀ v ∈ V, c * v = v * c := fun c hc v hv =>
    (Subgroup.mem_centralizer_iff.mp hc.2 v hv).symm
  have hCE : IsElemAbelian 2 C := isElemAbelian_mono151 inf_le_left hA.2.1
  have hBE : IsElemAbelian 2 (C ⊔ V) := isElemAbelian_sup_of_commute151b hCE hV hcomm
  have hBT : C ⊔ V ≤ T := sup_le (inf_le_left.trans hA.1) hVT
  have hle := card_le_two_pow_pRank151b hBT hBE
  have hcard := hA.2.2
  have hprod := (card_sup_mul_card_inf_of_commute151b C V hcomm).1
  have hinf : C ⊓ V = V ⊓ A := by
    ext x
    constructor
    · rintro ⟨⟨hxA, -⟩, hxV⟩
      exact ⟨hxV, hxA⟩
    · rintro ⟨hxV, hxA⟩
      refine ⟨⟨hxA, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩, hxV⟩
      have := hV.1
      exact setLike_mul_comm hv hxV
  rw [hinf] at hprod
  have h2 : Nat.card (C ⊔ V : Subgroup G) ≤ 2 * Nat.card A := by
    calc Nat.card (C ⊔ V : Subgroup G) ≤ 2 ^ CFSG.Open.pRank 2 T := hle
      _ = 2 * Nat.card A := by rw [← hcard]; ring
  calc Nat.card V * Nat.card C = Nat.card C * Nat.card V := mul_comm _ _
    _ = Nat.card (C ⊔ V : Subgroup G) * Nat.card (V ⊓ A : Subgroup G) := hprod.symm
    _ ≤ 2 * Nat.card A * Nat.card (V ⊓ A : Subgroup G) := Nat.mul_le_mul_right _ h2

theorem card_le_two_mul_of_corank_one151b {T V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVT : V ≤ T) (hTN : T ≤ Subgroup.normalizer (V : Set G))
    (hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hA : IsElemAbelianCorank T 1 A)
    (hA1 : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    Nat.card V ≤ 2 * Nat.card (autI hV A) *
      Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans hTN
  have h1 := card_autI_mul_card_inf hV hAN
  have h2 := card_mul_le_of_corank_one151b hV hVT hA
  have hinf : V ⊓ Subgroup.centralizer (A : Set G) = V ⊓ A := by
    refine le_antisymm (fun x hx => ⟨hx.1, inf_centralizer_le_of_corank_one151b hV hVT hJ hA hA1 hx⟩)
      (fun x hx => ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩)
    have := hA.2.1.1
    exact setLike_mul_comm ha hx.2
  rw [hinf]
  have hpos : 0 < Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := Nat.card_pos
  have h3 : Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) ≤
      2 * Nat.card (autI hV A) * Nat.card (V ⊓ A : Subgroup G) *
        Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
    calc Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G)
        ≤ 2 * Nat.card A * Nat.card (V ⊓ A : Subgroup G) := h2
      _ = 2 * (Nat.card (autI hV A) * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G)) *
          Nat.card (V ⊓ A : Subgroup G) := by rw [h1]
      _ = 2 * Nat.card (autI hV A) * Nat.card (V ⊓ A : Subgroup G) *
          Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by ring
  exact Nat.le_of_mul_le_mul_right h3 hpos

theorem card_eq_two_mul_of_corank_one151b {T V A M : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVT : V ≤ T) (hTN : T ≤ Subgroup.normalizer (V : Set G))
    (hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hA : IsElemAbelianCorank T 1 A)
    (hA1 : ¬ A ≤ Subgroup.centralizer (V : Set G)) (hAM : A ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hFF : ¬ IsFFModule (autI hV M)) :
    Nat.card V = 2 * Nat.card (autI hV A) *
      Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans hTN
  have hle := card_le_two_mul_of_corank_one151b hV hVT hTN hJ hA hA1
  have hA2 := isA2_autI hV hMN hAM hA.2.1 hA1
  have hlt : Nat.card (autI hV A) *
      Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) < Nat.card V := by
    by_contra hge
    push Not at hge
    refine hFF ⟨autI hV A, hA2.1, hA2.2.1, hA2.2.2, ?_⟩
    rw [card_fixV_autI hV hAN]
    exact hge
  set C : Subgroup G := V ⊓ Subgroup.centralizer (A : Set G) with hC
  have hCV : C ≤ V := inf_le_left
  have hVcard : Nat.card V = 2 ^ rk V := by
    have hp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
    exact card_eq_two_pow_of_isPGroup hp
  have hrel := Subgroup.relIndex_mul_card C V
  rw [inf_eq_left.2 hCV] at hrel
  have hdvd : C.relIndex V ∣ 2 ^ rk V := by
    rw [← hVcard, ← hrel]
    exact Dvd.intro _ rfl
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hAcard : Nat.card (autI hV A) = 2 ^ rk (autI hV A) := B1.card_elemAbelian hA2.2.2
  set k := rk (autI hV A) with hk
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hVeq : Nat.card V = 2 ^ b * Nat.card C := by rw [← hrel, hb]
  have h1 : 2 ^ k < 2 ^ b := by
    have := hlt
    rw [hAcard, hVeq] at this
    exact Nat.lt_of_mul_lt_mul_right this
  have h2 : 2 ^ b ≤ 2 * 2 ^ k := by
    have := hle
    rw [hAcard, hVeq] at this
    have h' : 2 ^ b * Nat.card C ≤ 2 * 2 ^ k * Nat.card C := this
    exact Nat.le_of_mul_le_mul_right h' hCpos
  have hkb : k < b := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
  have hbk : b ≤ k + 1 := by
    have : 2 ^ b ≤ 2 ^ (k + 1) := by rw [pow_succ]; linarith
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hbeq : b = k + 1 := by omega
  rw [hVeq, hbeq, hAcard, pow_succ]
  ring

theorem commSeries_three_eq_bot_of_card_le_four151b {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {E : Subgroup (MulAut W)} (hE : IsElemAbelian2 E)
    (hcard : Nat.card E ≤ 4) : commSeries E 3 = ⊥ := by
  have hEcard : Nat.card E = 2 ^ rk E := B1.card_elemAbelian hE
  have hrk : rk E ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ rk E := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain h0 | h1 | h2 : rk E = 0 ∨ rk E = 1 ∨ rk E = 2 := by omega
  ·
    have hE1 : Nat.card E = 1 := by rw [hEcard, h0]; norm_num
    have hbot : E = ⊥ := Subgroup.card_eq_one.mp hE1
    subst hbot
    have h1 : commSub (⊤ : Subgroup W) (⊥ : Subgroup (MulAut W)) = ⊥ :=
      commSub_eq_bot_iff.mpr (by simp [B1.fixV_bot])
    show commSub (commSub (commSub ⊤ ⊥) ⊥) ⊥ = ⊥
    rw [h1, commSub_bot_left, commSub_bot_left]
  ·
    have hE2 : Nat.card E = 2 := by rw [hEcard, h1]; norm_num
    obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
      rw [this, Subgroup.card_bot] at hE2
      omega
    have ha2 : a ^ 2 = 1 := hE.2 a haE
    have hz : Subgroup.zpowers a ≤ E := Subgroup.zpowers_le.mpr haE
    have hzcard : Nat.card (Subgroup.zpowers a) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1]
    have hEz : Subgroup.zpowers a = E := Subgroup.eq_of_le_of_card_ge hz (by omega)
    rw [← hEz]
    have hq : commSeries (Subgroup.zpowers a) 2 = ⊥ :=
      commSub_commSub_self hW ha2 (W := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
    exact commSeries_eq_bot_of_le (by norm_num) hq
  · have hE4 : Nat.card E = 4 := by rw [hEcard, h2]; norm_num
    exact commSeries_three_eq_bot_of_card_four hW hE hE4

end Counting

end CFSG.Quasithin
