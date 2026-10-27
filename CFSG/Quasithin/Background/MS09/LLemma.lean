module

public import CFSG.Quasithin.Background.MS09.Minimal
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.C64Dihedral
public import CFSG.Quasithin.Background.G64Linear

public section

namespace CFSG.Quasithin.MS09

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B6

variable {G : Type} [Group G]

namespace LLemma

private theorem conjSub_conjSub_inv (x : G) (K : Subgroup G) :
    B6.conjSub x (B6.conjSub x⁻¹ K) = K := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

private theorem conjSub_inv_conjSub (x : G) (K : Subgroup G) :
    B6.conjSub x⁻¹ (B6.conjSub x K) = K := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

private theorem conjSub_of_mem {x : G} {K : Subgroup G} (hx : x ∈ K) : B6.conjSub x K = K :=
  conjSub_eq_self (Subgroup.le_normalizer hx)

private theorem mem_normalizer_of_conjSub_eq {x : G} {K : Subgroup G} (h : B6.conjSub x K = K) :
    x ∈ Subgroup.normalizer (K : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

private def star (H A U : Subgroup G) : Subgroup G :=
  ⨆ (g : G) (_ : g ∈ H ∧ B6.conjSub g A ≤ U), B6.conjSub g A

variable {H A U U' : Subgroup G}

private theorem star_le (H A U : Subgroup G) : star H A U ≤ U :=
  iSup₂_le fun _ hg => hg.2

private theorem le_star {g : G} (hg : g ∈ H) (hgU : B6.conjSub g A ≤ U) :
    B6.conjSub g A ≤ star H A U :=
  le_iSup₂_of_le (f := fun (g : G) (_ : g ∈ H ∧ B6.conjSub g A ≤ U) => B6.conjSub g A) g
    ⟨hg, hgU⟩ le_rfl

private theorem star_mono (h : U ≤ U') : star H A U ≤ star H A U' :=
  iSup₂_le fun _ hg => le_star hg.1 (hg.2.trans h)

private theorem le_star_self (hAU : A ≤ U) : A ≤ star H A U := by
  have h := le_star (H := H) (A := A) (U := U) (g := 1) H.one_mem (by rwa [conjSub_one])
  rwa [conjSub_one] at h

private theorem star_le_star_of_le (h : star H A U ≤ U') : star H A U ≤ star H A U' :=
  iSup₂_le fun _ hg => le_star hg.1 ((le_star hg.1 hg.2).trans h)

private theorem conjSub_star_le {x : G} (hx : x ∈ H) :
    B6.conjSub x (star H A U) ≤ star H A (B6.conjSub x U) := by
  have key : star H A U ≤ B6.conjSub x⁻¹ (star H A (B6.conjSub x U)) := by
    refine iSup₂_le fun g hg => ?_
    rw [← (B6.conjSub x).le_iff_le, conjSub_conjSub_inv, ← conjSub_mul]
    exact le_star (H.mul_mem hx hg.1) (by rw [conjSub_mul]; exact (B6.conjSub x).monotone hg.2)
  have := (B6.conjSub x).monotone key
  rwa [conjSub_conjSub_inv] at this

private theorem conjSub_star {x : G} (hx : x ∈ H) :
    B6.conjSub x (star H A U) = star H A (B6.conjSub x U) := by
  refine le_antisymm (conjSub_star_le hx) ?_
  have h := conjSub_star_le (A := A) (U := B6.conjSub x U) (H.inv_mem hx)
  rw [conjSub_inv_conjSub] at h
  have := (B6.conjSub x).monotone h
  rwa [conjSub_conjSub_inv] at this

private theorem mem_normalizer_star {x : G} (hx : x ∈ H)
    (hxU : x ∈ Subgroup.normalizer (U : Set G)) :
    x ∈ Subgroup.normalizer (star H A U : Set G) := by
  refine mem_normalizer_of_conjSub_eq ?_
  rw [conjSub_star hx, conjSub_eq_self hxU]

private theorem isPGroup_star (hU : IsPGroup 2 U) : IsPGroup 2 (star H A U) :=
  hU.to_le (star_le H A U)

variable [Finite G]

private theorem exists_conjSub_le {S M T₀ : Subgroup G} (hSM : IsSylowTwoOf S M)
    (hT₀ : IsPGroup 2 T₀) (hT₀M : T₀ ≤ M) : ∃ m ∈ M, B6.conjSub m T₀ ≤ S := by
  obtain ⟨S', hS', hT₀S'⟩ := exists_isSylowTwoOf_ge hT₀ hT₀M
  obtain ⟨g, hg, rfl⟩ := isSylowTwoOf_exists_conj hSM hS'
  refine ⟨g⁻¹, M.inv_mem hg, ?_⟩
  have := (B6.conjSub g⁻¹).monotone hT₀S'
  rwa [conjSub_inv_conjSub] at this

section Setting

variable {S M : Subgroup G} (hS : IsSylowTwoOf S H) (hM : IsUniqueMaxSub H S M)
  (hAS : A ≤ S) (hAO : ¬ A ≤ pCoreOf 2 H)

include hS hM hAS hAO

private theorem conjSub_ne {x : G} (hx : x ∈ H) (hxM : x ∉ M) : B6.conjSub x M ≠ M := by
  intro hxe
  have hxn := mem_normalizer_of_conjSub_eq hxe
  have hMH : M ≤ H := hM.lt.le
  have hK : H ⊓ Subgroup.normalizer (M : Set G) = H := by
    by_contra hne
    exact hxM (hM.le_of_lt (le_inf (hM.le.trans hMH) (hM.le.trans Subgroup.le_normalizer))
      (lt_of_le_of_ne inf_le_left hne) ⟨hx, hxn⟩)
  have hHn : H ≤ Subgroup.normalizer (M : Set G) := by
    rw [← hK]
    exact inf_le_right
  rcases hM.dichotomy hS le_rfl hMH hHn with h1 | h1
  · rw [sup_eq_right.mpr hM.le] at h1
    exact absurd h1 hM.lt.ne
  · have hSM : S ⊓ M = S := inf_eq_left.mpr hM.le
    rw [hSM] at h1
    exact hAO (hAS.trans h1)

private theorem normalizer_star_le : H ⊓ Subgroup.normalizer (star H A S : Set G) ≤ M := by
  have hSH : S ≤ H := hS.1
  have hSK : S ≤ H ⊓ Subgroup.normalizer (star H A S : Set G) :=
    le_inf hSH fun s hs => mem_normalizer_star (hSH hs) (Subgroup.le_normalizer hs)
  by_cases hK : H ⊓ Subgroup.normalizer (star H A S : Set G) = H
  · exfalso
    have hHn : H ≤ Subgroup.normalizer (star H A S : Set G) := fun x hx => by
      rw [← hK] at hx
      exact hx.2
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((star_le H A S).trans hSH) hHn (isPGroup_star hS.2.1)
    exact hAO ((le_star_self hAS).trans hle)
  · exact hM.le_of_lt hSK (lt_of_le_of_ne inf_le_left hK)

private def cand (H S M : Subgroup G) : Set (Subgroup G) :=
  {T | ∃ h ∈ H, B6.conjSub h M ≠ M ∧ IsSylowTwoOf T (B6.conjSub h M ⊓ M) ∧ T ≤ S}

omit hAS hAO in
private theorem mem_cand_of {x : G} (hx : x ∈ H) (hxM : B6.conjSub x M ≠ M) {T₀ : Subgroup G}
    (hT₀ : IsSylowTwoOf T₀ (B6.conjSub x M ⊓ M)) :
    ∃ T ∈ cand H S M, Nat.card (star H A T) = Nat.card (star H A T₀) := by
  have hMH : M ≤ H := hM.lt.le
  have hSM : IsSylowTwoOf S M := isSylowTwoOf_mono hS hM.le hMH
  obtain ⟨m, hm, hmT⟩ := exists_conjSub_le hSM hT₀.2.1 (hT₀.1.trans inf_le_right)
  have hmM : B6.conjSub m M = M := conjSub_of_mem hm
  refine ⟨B6.conjSub m T₀, ⟨m * x, H.mul_mem (hMH hm) hx, ?_, ?_, hmT⟩, ?_⟩
  · rw [conjSub_mul]
    intro he
    apply hxM
    have hm' : B6.conjSub m⁻¹ M = M := conjSub_of_mem (M.inv_mem hm)
    have := congrArg (B6.conjSub m⁻¹) he
    rwa [conjSub_inv_conjSub, hm'] at this
  · have h := isSylowTwoOf_conjSub hT₀ m
    rwa [(B6.conjSub m).map_inf, hmM, ← conjSub_mul] at h
  · rw [← conjSub_star (hMH hm), card_conjSub]

omit hAS hAO in
private theorem cand_nonempty (hAO' : ∃ x ∈ H, B6.conjSub x M ≠ M) : (cand H S M).Nonempty := by
  obtain ⟨x, hx, hxM⟩ := hAO'
  obtain ⟨T₀, hT₀, -⟩ := exists_isSylowTwoOf_ge (J := B6.conjSub x M ⊓ M)
    (IsPGroup.of_bot (p := 2) (G := G)) bot_le
  obtain ⟨T, hT, -⟩ := mem_cand_of (A := ⊥) hS hM hx hxM hT₀
  exact ⟨T, hT⟩

theorem lLemma : ∃ L L₀ : Subgroup G, L ≤ H ∧ A ≤ L ∧
    IsUniqueMaxSub L (A ⊔ pCoreOf 2 L) L₀ ∧
    (∀ x ∈ L, x ∉ L₀ → A ⊔ B6.conjSub x A ⊔ pCoreOf 2 L = L) ∧
    ∀ g ∈ H, ¬ L ≤ B6.conjSub g M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMH : M ≤ H := hM.lt.le
  have hSH : S ≤ H := hS.1
  obtain ⟨x₀, hx₀, hx₀M⟩ := SetLike.exists_of_lt hM.lt
  have hne := cand_nonempty hS hM ⟨x₀, hx₀, conjSub_ne hS hM hAS hAO hx₀ hx₀M⟩
  obtain ⟨T, hTc, hTmax⟩ := Set.exists_max_image (cand H S M)
    (fun T => Nat.card (star H A T)) (Set.toFinite _) hne
  obtain ⟨h₀, hh₀, hY, hTsyl, hTS⟩ := hTc
  have hmax : ∀ x ∈ H, B6.conjSub x M ≠ M → ∀ K : Subgroup G, IsPGroup 2 K →
      K ≤ B6.conjSub x M ⊓ M → Nat.card (star H A K) ≤ Nat.card (star H A T) := by
    intro x hx hxM K hK hKle
    obtain ⟨T₀, hT₀, hKT₀⟩ := exists_isSylowTwoOf_ge hK hKle
    obtain ⟨T', hT', hcard⟩ := mem_cand_of (A := A) hS hM hx hxM hT₀
    calc Nat.card (star H A K) ≤ Nat.card (star H A T₀) :=
          Subgroup.card_le_of_le (star_mono hKT₀)
      _ = Nat.card (star H A T') := hcard.symm
      _ ≤ Nat.card (star H A T) := hTmax T' hT'
  have hYH : B6.conjSub h₀ M ≤ H := by
    have := (B6.conjSub h₀).monotone hMH
    rwa [conjSub_of_mem hh₀] at this
  have hTY : T ≤ B6.conjSub h₀ M := hTsyl.1.trans inf_le_left
  have hTM : T ≤ M := hTsyl.1.trans inf_le_right
  have hSY : IsSylowTwoOf (B6.conjSub h₀ S) (B6.conjSub h₀ M) := by
    have h1 := isSylowTwoOf_conjSub hS h₀
    rw [conjSub_of_mem hh₀] at h1
    exact isSylowTwoOf_mono h1 ((B6.conjSub h₀).monotone hM.le) hYH
  obtain ⟨S'', hS'', hTS''⟩ := exists_isSylowTwoOf_ge hTsyl.2.1 hTY
  obtain ⟨y, hy, rfl⟩ := isSylowTwoOf_exists_conj hSY hS''
  have hh : y * h₀ ∈ H := H.mul_mem (hYH hy) hh₀
  have hShY : B6.conjSub (y * h₀) S ≤ B6.conjSub h₀ M := by rw [conjSub_mul]; exact hS''.1
  have hTSh : T ≤ B6.conjSub (y * h₀) S := by rw [conjSub_mul]; exact hTS''
  have hShH : B6.conjSub (y * h₀) S ≤ H := by
    have := (B6.conjSub (y * h₀)).monotone hSH
    rwa [conjSub_of_mem hh] at this
  have hTlt : T < B6.conjSub (y * h₀) S := by
    refine lt_of_le_of_ne hTSh fun hTe => hY ?_
    have hShM : B6.conjSub (y * h₀) S ≤ M := hTe ▸ hTM
    have hMh := hM.conjSub (y * h₀)
    rw [conjSub_of_mem hh] at hMh
    have hYlt : B6.conjSub h₀ M < H := by
      have := (B6.conjSub h₀).strictMono hM.lt
      rwa [conjSub_of_mem hh₀] at this
    have h1 : M = B6.conjSub (y * h₀) M :=
      Subgroup.eq_of_le_of_card_ge (hMh.le_of_lt hShM hM.lt) (by rw [card_conjSub])
    have h2 : B6.conjSub h₀ M = B6.conjSub (y * h₀) M :=
      Subgroup.eq_of_le_of_card_ge (hMh.le_of_lt hShY hYlt) (by rw [card_conjSub, card_conjSub])
    rw [h2, ← h1]
  have hSh2 : IsPGroup 2 (B6.conjSub (y * h₀) S) := hS.2.1.map (MulAut.conj (y * h₀)).toMonoidHom
  obtain ⟨g, hgSh, hgT, hgnT⟩ := C64Dihedral.exists_mem_normalizer_not_mem hSh2 hTlt
  have hgH : g ∈ H := hShH hgSh
  have hgM : g ∉ M := by
    intro hgM
    have hQ : IsPGroup 2 ↥(Subgroup.zpowers g ⊔ T) :=
      IsPGroup.to_sup_of_normal_right' (hSh2.to_le (Subgroup.zpowers_le.mpr hgSh))
        hTsyl.2.1 (Subgroup.zpowers_le.mpr hgT)
    have hQle : Subgroup.zpowers g ⊔ T ≤ B6.conjSub h₀ M ⊓ M :=
      sup_le (Subgroup.zpowers_le.mpr ⟨hShY hgSh, hgM⟩) hTsyl.1
    have he := G64.IsSylowTwoOf.eq_of_le hTsyl le_sup_right hQle hQ
    have hmem : g ∈ Subgroup.zpowers g ⊔ T := Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
    rw [he] at hmem
    exact hgnT hmem
  have hTH : T ≤ H := hTS.trans hSH
  have hTN : T ≤ H ⊓ Subgroup.normalizer (star H A T : Set G) :=
    le_inf hTH fun t ht => mem_normalizer_star (hTH ht) (Subgroup.le_normalizer ht)
  have hsTN : star H A T ≤ H ⊓ Subgroup.normalizer (star H A T : Set G) :=
    (star_le H A T).trans hTN
  have hgN : g ∈ H ⊓ Subgroup.normalizer (star H A T : Set G) :=
    ⟨hgH, mem_normalizer_star hgH hgT⟩
  have hTS' : star H A T ≠ star H A S := by
    intro he
    apply hgM
    exact normalizer_star_le hS hM hAS hAO (by rw [← he]; exact hgN)
  have hTS₁ : T ≤ S ⊓ (H ⊓ Subgroup.normalizer (star H A T : Set G)) := le_inf hTS hTN
  have hTS₁' : star H A T ≠ star H A (S ⊓ (H ⊓ Subgroup.normalizer (star H A T : Set G))) := by
    intro he
    by_cases hS₁S : S ⊓ (H ⊓ Subgroup.normalizer (star H A T : Set G)) = S
    · exact hTS' (he.trans (by rw [hS₁S]))
    · obtain ⟨s, hsS, hsn, hsnS₁⟩ := C64Dihedral.exists_mem_normalizer_not_mem hS.2.1
        (lt_of_le_of_ne inf_le_left hS₁S)
      apply hsnS₁
      refine ⟨hsS, hSH hsS, ?_⟩
      have := mem_normalizer_star (A := A) (hSH hsS) hsn
      rwa [← he] at this
  obtain ⟨b, hb, hBS₁, hBT⟩ : ∃ b ∈ H, B6.conjSub b A ≤
      S ⊓ (H ⊓ Subgroup.normalizer (star H A T : Set G)) ∧ ¬ B6.conjSub b A ≤ T := by
    by_contra hcon
    push Not at hcon
    apply hTS₁'
    refine le_antisymm (star_mono hTS₁) (iSup₂_le fun c hc => ?_)
    exact le_star hc.1 (hcon c hc.1 hc.2)
  have hBS : B6.conjSub b A ≤ S := hBS₁.trans inf_le_left
  have hBN : B6.conjSub b A ≤ H ⊓ Subgroup.normalizer (star H A T : Set G) :=
    hBS₁.trans inf_le_right
  have hB2 : IsPGroup 2 (B6.conjSub b A) := hS.2.1.to_le hBS
  have hBsT : ¬ B6.conjSub b A ≤ star H A T := fun h => hBT (h.trans (star_le H A T))
  have hBsTS : B6.conjSub b A ⊔ star H A T ≤ S := sup_le hBS ((star_le H A T).trans hTS)
  have huniq : ∀ x ∈ H, B6.conjSub b A ⊔ star H A T ≤ B6.conjSub x M → B6.conjSub x M = M := by
    intro x hx hle
    by_contra hxM
    have h1 := hmax x hx hxM (B6.conjSub b A ⊔ star H A T) (hS.2.1.to_le hBsTS)
      (le_inf hle (hBsTS.trans hM.le))
    have h2 : B6.conjSub b A ⊔ star H A T ≤ star H A (B6.conjSub b A ⊔ star H A T) :=
      sup_le (le_star hb le_sup_left) (star_le_star_of_le le_sup_right)
    have h3 : ¬ Nat.card ↥(B6.conjSub b A ⊔ star H A T) ≤ Nat.card (star H A T) := fun hc =>
      hBsT ((Subgroup.eq_of_le_of_card_ge le_sup_right hc) ▸ le_sup_left)
    have h4 := Subgroup.card_le_of_le h2
    omega
  obtain ⟨z, ⟨hzN, hzM⟩, hzmin⟩ := Set.exists_min_image
    {z : G | z ∈ H ⊓ Subgroup.normalizer (star H A T : Set G) ∧ z ∉ M}
    (fun z => Nat.card ↥(B6.conjSub b A ⊔ Subgroup.zpowers z ⊔ star H A T))
    (Set.toFinite _) ⟨g, hgN, hgM⟩
  set L₁ := B6.conjSub b A ⊔ Subgroup.zpowers z ⊔ star H A T with hL₁def
  have hL₁N : L₁ ≤ H ⊓ Subgroup.normalizer (star H A T : Set G) :=
    sup_le (sup_le hBN (Subgroup.zpowers_le.mpr hzN)) hsTN
  have hL₁H : L₁ ≤ H := hL₁N.trans inf_le_left
  have hzL₁ : z ∈ L₁ := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hBL₁ : B6.conjSub b A ≤ L₁ := le_sup_left.trans le_sup_left
  have hsTL₁ : star H A T ≤ L₁ := le_sup_right
  have hgen : ∀ z' ∈ L₁, z' ∉ M →
      B6.conjSub b A ⊔ Subgroup.zpowers z' ⊔ star H A T = L₁ := by
    intro z' hz' hz'M
    exact Subgroup.eq_of_le_of_card_ge
      (sup_le (sup_le hBL₁ (Subgroup.zpowers_le.mpr hz')) hsTL₁) (hzmin z' ⟨hL₁N hz', hz'M⟩)
  have hnotM : ∀ x ∈ H, ¬ L₁ ≤ B6.conjSub x M := by
    intro x hx hle
    have := huniq x hx ((sup_le hBL₁ hsTL₁).trans hle)
    exact hzM (this ▸ hle hzL₁)
  have hsTO : star H A T ≤ pCoreOf 2 L₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hsTL₁ (hL₁N.trans inf_le_right)
      (isPGroup_star hTsyl.2.1)
  have hkey : ∀ K : Subgroup G, B6.conjSub b A ⊔ star H A T ≤ K → K < L₁ → K ≤ M := by
    intro K hK hKL
    by_contra hKM
    obtain ⟨z', hz'K, hz'M⟩ := SetLike.not_le_iff_exists.mp hKM
    have he := hgen z' (hKL.le hz'K) hz'M
    refine hKL.ne (le_antisymm hKL.le ?_)
    rw [← he]
    exact sup_le (sup_le (le_sup_left.trans hK) (Subgroup.zpowers_le.mpr hz'K))
      (le_sup_right.trans hK)
  have hO2L₁ : B6.conjSub b A ⊔ pCoreOf 2 L₁ < L₁ := by
    refine lt_of_le_of_ne (sup_le hBL₁ (CFSG.LieType.BorelTits.pCoreOf_le 2 L₁)) fun he => ?_
    have hL2 : IsPGroup 2 ↥L₁ := by
      rw [← he]
      exact IsPGroup.to_sup_of_normal_right' hB2
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁)
        (hBL₁.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₁))
    obtain ⟨S', hS', hL₁S'⟩ := exists_isSylowTwoOf_ge hL2 hL₁H
    obtain ⟨x, hx, rfl⟩ := isSylowTwoOf_exists_conj hS hS'
    exact hnotM x hx (hL₁S'.trans ((B6.conjSub x).monotone hM.le))
  have hBO : B6.conjSub b A ⊔ pCoreOf 2 L₁ ≤ M :=
    hkey _ (sup_le_sup_left hsTO _) hO2L₁
  have hUM : IsUniqueMaxSub L₁ (B6.conjSub b A ⊔ pCoreOf 2 L₁) (L₁ ⊓ M) := by
    refine ⟨le_inf hO2L₁.le hBO, lt_of_le_of_ne inf_le_left fun he => hzM ?_,
      fun K hK hKL => le_inf hKL.le (hkey K ((sup_le_sup_left hsTO _).trans hK) hKL)⟩
    have : z ∈ L₁ ⊓ M := by rw [he]; exact hzL₁
    exact this.2
  have hNM : ∀ x ∈ L₁, x ∉ L₁ ⊓ M →
      B6.conjSub b A ⊔ B6.conjSub x (B6.conjSub b A) ⊔ pCoreOf 2 L₁ = L₁ := by
    intro x hx hxM'
    have hxM : x ∉ M := fun h => hxM' ⟨hx, h⟩
    have hxH : x ∈ H := hL₁H hx
    have hxs : B6.conjSub x (star H A T) = star H A T := conjSub_eq_self (hL₁N hx).2
    have hxB : ¬ B6.conjSub x (B6.conjSub b A) ≤ M := by
      intro hle
      apply conjSub_ne hS hM hAS hAO hxH hxM
      have h1 : B6.conjSub b A ⊔ star H A T ≤ B6.conjSub x⁻¹ M := by
        rw [← (B6.conjSub x).le_iff_le, conjSub_conjSub_inv, (B6.conjSub x).map_sup, hxs]
        exact sup_le hle ((star_le H A T).trans hTM)
      have h2 := congrArg (B6.conjSub x) (huniq x⁻¹ (H.inv_mem hxH) h1)
      rw [conjSub_conjSub_inv] at h2
      exact h2.symm
    obtain ⟨w, hwB, hwM⟩ := SetLike.not_le_iff_exists.mp hxB
    have hxBL : B6.conjSub x (B6.conjSub b A) ≤ L₁ := by
      have := (B6.conjSub x).monotone hBL₁
      rwa [conjSub_of_mem hx] at this
    refine le_antisymm (sup_le (sup_le hBL₁ hxBL) (CFSG.LieType.BorelTits.pCoreOf_le 2 L₁)) ?_
    calc L₁ = B6.conjSub b A ⊔ Subgroup.zpowers w ⊔ star H A T := (hgen w (hxBL hwB) hwM).symm
      _ ≤ B6.conjSub b A ⊔ B6.conjSub x (B6.conjSub b A) ⊔ pCoreOf 2 L₁ :=
        sup_le (sup_le (le_sup_left.trans le_sup_left)
          (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_sup_right hwB))))
          (hsTO.trans le_sup_right)
  clear_value L₁
  refine ⟨B6.conjSub b⁻¹ L₁, B6.conjSub b⁻¹ (L₁ ⊓ M), ?_, ?_, ?_, ?_, ?_⟩
  · have := (B6.conjSub b⁻¹).monotone hL₁H
    rwa [conjSub_of_mem (H.inv_mem hb)] at this
  · have := (B6.conjSub b⁻¹).monotone hBL₁
    rwa [conjSub_inv_conjSub] at this
  · have := hUM.conjSub b⁻¹
    rwa [(B6.conjSub b⁻¹).map_sup, conjSub_inv_conjSub, ← pCoreOf_conjSub] at this
  · intro x hx hxL₀
    have hx' : b * x * b⁻¹ ∈ L₁ := by
      rw [mem_conjSub, inv_inv] at hx
      exact hx
    have hxL₀' : b * x * b⁻¹ ∉ L₁ ⊓ M := fun h => hxL₀ (by rw [mem_conjSub, inv_inv]; exact h)
    have h1 := congrArg (B6.conjSub b⁻¹) (hNM _ hx' hxL₀')
    rw [(B6.conjSub b⁻¹).map_sup, (B6.conjSub b⁻¹).map_sup, conjSub_inv_conjSub,
      ← pCoreOf_conjSub, ← conjSub_mul, ← conjSub_mul] at h1
    have e : b⁻¹ * (b * x * b⁻¹) * b = x := by group
    rwa [e] at h1
  · intro x hx hle
    apply hnotM (b * x) (H.mul_mem hb hx)
    have := (B6.conjSub b).monotone hle
    rwa [conjSub_conjSub_inv, ← conjSub_mul] at this

end Setting

end LLemma

end CFSG.Quasithin.MS09

end
