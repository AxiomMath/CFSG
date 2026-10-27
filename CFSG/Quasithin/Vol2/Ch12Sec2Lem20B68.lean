module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7One
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem21Stmts
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

namespace Lem20B68

theorem map_frattini_mulEquiv {P Q : Type*} [Group P] [Group Q] (ι : P ≃* Q) :
    (frattini P).map ι.toMonoidHom = frattini Q := by
  refine le_antisymm ?_ fun x hx => ?_
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective ι.surjective
  · have h := frattini_le_comap_frattini_of_surjective (φ := ι.symm.toMonoidHom) ι.symm.surjective
    exact ⟨ι.symm x, h hx, by simp⟩

section Abstract

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem sup_eq_top_of_pi {p : ℕ} (hZ : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = p)
    {P T : Subgroup X} (hP : ¬ p ∣ P.index) (hT : ¬ 2 ∣ T.index) : P ⊔ T = ⊤ := by
  by_contra hne
  have h1 : (P ⊔ T).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd h1
  rcases hZ q hq (hqd.trans (P ⊔ T).index_dvd_card) with rfl | rfl
  · exact hT (hqd.trans (Subgroup.index_dvd_of_le le_sup_right))
  · exact hP (hqd.trans (Subgroup.index_dvd_of_le le_sup_left))

variable {T M : Subgroup X}

theorem sylow_structure (h : MinParabolic (⊤ : Subgroup X) T M) (hsolv : Group.IsSolvable X) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∀ P : Subgroup X, IsPGroup p P → ¬ p ∣ P.index →
      P ⊔ T = ⊤ ∧ P ⊓ M = (frattini ↥P).map P.subtype := by
  obtain ⟨p, hp, hp2, hO, hJ, hne, hirr⟩ := h.solvable_structure hsolv
  obtain ⟨q, hq, hq2, hZq⟩ := h.exists_odd_prime_of_solvable hsolv
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := kerIn M ⊤ with hJdef
  have hpX : p ∣ Nat.card X := by
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hyp : IsPGroup p (CFSG.Open.pCore p (X ⧸ J)) :=
      CFSG.LieType.BorelTits.pCore_isPGroup (G := X ⧸ J) p
    have h1 : (⟨y, hy⟩ : ↥(CFSG.Open.pCore p (X ⧸ J))) ≠ 1 := hy1
    have hdvd : p ∣ Nat.card (X ⧸ J) := by
      have hne1 : Nontrivial ↥(CFSG.Open.pCore p (X ⧸ J)) := ⟨⟨_, _, h1⟩⟩
      obtain ⟨n, hn⟩ := hyp.exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero, Nat.card_eq_one_iff_unique] at hn
        exact h1 (hn.1.elim _ _)
      exact (dvd_pow_self p hn0).trans (hn ▸ Subgroup.card_subgroup_dvd_card _)
    exact hdvd.trans (Subgroup.card_quotient_dvd_card J)
  have hZ : ∀ r : ℕ, r.Prime → r ∣ Nat.card X → r = 2 ∨ r = p := by
    have hpq : p = q := (hZq p hp hpX).resolve_left hp2
    intro r hr hrX
    rw [hpq]
    exact hZq r hr hrX
  refine ⟨p, hp, hp2, fun P hP hPi => ?_⟩
  have hTi : ¬ 2 ∣ T.index := fun h2 =>
    h.isSylow.2.2 (by rwa [← Subgroup.relIndex_top_right] at h2)
  have hPT : P ⊔ T = ⊤ := sup_eq_top_of_pi hZ hPi hTi
  refine ⟨hPT, ?_⟩
  set N₂ := CFSG.Open.pCore 2 X with hN₂
  set π := QuotientGroup.mk' N₂ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hN₂J : N₂ ≤ J := h.pCore_le_kerIn
  have hkerπ : π.ker ≤ J := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hN₂J
  set Kp := CFSG.Open.pCore p (X ⧸ N₂) with hKp
  have hKpp : IsPGroup p Kp := CFSG.LieType.BorelTits.pCore_isPGroup (G := X ⧸ N₂) p
  have hPO : P ≤ O2p X p := by
    intro x hx
    obtain ⟨k, hk⟩ := (B6.upperTwo_eq_top_iff (O2p X p)).mp hO x
    refine B6.mem_of_pow_mem_of_coprime hk ?_
    obtain ⟨m, hm⟩ := hP ⟨x, hx⟩
    have hxm : x ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hxm)
      (Nat.coprime_pow_primes m k hp Nat.prime_two hp2)
  have hπP : P.map π = Kp := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_comap.mp (hPO hx)
    · have hPmi : ¬ p ∣ (P.map π).index := fun hd => hPi (hd.trans (Subgroup.index_map_dvd P hπs))
      have : Kp.Normal := CFSG.LieType.BorelTits.pCore_normal p
      exact hKpp.le_sylow_of_normal ((hP.map π).toSylow hPmi)
  have hinj : Function.Injective (π.subgroupMap P) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : π x = 1 := congrArg Subtype.val hx
    have h2 : (x : X) ∈ N₂ := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    obtain ⟨m, hm⟩ := hP x
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := X) 2) ⟨x, h2⟩
    have hm' : (x : X) ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hk' : (x : X) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_of_pow_eq_one hk')
    rw [Nat.coprime_pow_primes m k hp Nat.prime_two hp2] at h3
    exact Subtype.ext (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3))
  set e : ↥P ≃* ↥(P.map π) :=
    MulEquiv.ofBijective (π.subgroupMap P) ⟨hinj, π.subgroupMap_surjective P⟩ with he
  have hΦPmap : (frattini ↥(P.map π)).map (P.map π).subtype = J.map π := by
    rw [hJ]
    exact congrArg (fun A : Subgroup (X ⧸ N₂) => (frattini ↥A).map A.subtype) hπP
  have hΦJ : (frattini ↥P).map P.subtype ≤ J := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := frattini_le_comap_frattini_of_surjective (π.subgroupMap_surjective P) hx
    have h2 : π (x : X) ∈ (frattini ↥(P.map π)).map (P.map π).subtype := ⟨_, h1, rfl⟩
    rw [hΦPmap] at h2
    have h3 := Subgroup.mem_comap.mpr h2
    rwa [B6.comap_map_eq_of_ker_le hkerπ] at h3
  have hPJ : P ⊓ J ≤ (frattini ↥P).map P.subtype := by
    rintro x ⟨hxP, hxJ⟩
    have h1 : π x ∈ (frattini ↥(P.map π)).map (P.map π).subtype := by
      rw [hΦPmap]
      exact Subgroup.mem_map_of_mem π hxJ
    obtain ⟨y, hy, hyx⟩ := h1
    have hye : y = e ⟨x, hxP⟩ := Subtype.ext hyx
    have h2 := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom)
      e.symm.surjective hy
    rw [Subgroup.mem_comap, hye] at h2
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h2
    exact ⟨⟨x, hxP⟩, h2, rfl⟩
  set φ := QuotientGroup.mk' J with hφ
  have hJM : J ≤ M := kerIn_le
  have hkerφ : φ.ker ≤ M := by
    rw [hφ, QuotientGroup.ker_mk']
    exact hJM
  have hPφ : P.map φ ≤ CFSG.Open.pCore p (X ⧸ J) := by
    have hO2pφ : IsPGroup p ((O2p X p).map φ) := by
      rintro ⟨_, ⟨x, hx, rfl⟩⟩
      obtain ⟨m, hm⟩ := hKpp ⟨π x, Subgroup.mem_comap.mp hx⟩
      refine ⟨m, Subtype.ext ?_⟩
      have h1 : π (x ^ p ^ m) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hm
      have h2 : x ^ p ^ m ∈ J := hN₂J (by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1)
      show φ x ^ p ^ m = 1
      rw [← map_pow, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h2
    have hn : ((O2p X p).map φ).Normal :=
      Subgroup.Normal.map inferInstance φ (QuotientGroup.mk'_surjective _)
    exact (Subgroup.map_mono hPO).trans (CFSG.LieType.BorelTits.le_pCore p hn hO2pφ)
  have hpn : Subgroup.normalizer (CFSG.Open.pCore p (X ⧸ J) : Set (X ⧸ J)) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr (CFSG.LieType.BorelTits.pCore_normal p)
  have hSirr := hirr (CFSG.Open.pCore p (X ⧸ J) ⊓ M.map φ) inf_le_left
    ((le_inf (le_top.trans hpn.ge) ((Subgroup.map_mono h.le).trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf)
  have hPMJ : P ⊓ M ≤ J := by
    rcases hSirr with hS | hS
    · rintro x ⟨hxP, hxM⟩
      have h1 : φ x ∈ CFSG.Open.pCore p (X ⧸ J) ⊓ M.map φ :=
        ⟨hPφ ⟨x, hxP, rfl⟩, ⟨x, hxM, rfl⟩⟩
      rw [hS, Subgroup.mem_bot, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    · exfalso
      have hPM : P ≤ M := by
        intro x hx
        have h1 : φ x ∈ M.map φ := (inf_eq_left.mp hS) (hPφ ⟨x, hx, rfl⟩)
        have h2 := Subgroup.mem_comap.mpr h1
        rwa [B6.comap_map_eq_of_ker_le hkerφ] at h2
      have hMtop : M = ⊤ := top_le_iff.mp (hPT ▸ sup_le hPM h.le)
      exact h.maximal.1.ne hMtop
  exact le_antisymm (fun x hx => hPJ ⟨hx.1, hPMJ hx⟩)
    (le_inf (Subgroup.map_subtype_le _) (hΦJ.trans hJM))

end Abstract

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_of_minParabolic {H T M : Subgroup G} (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable ↥H) :
    ∃ (P : Subgroup G) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsPGroup p ↥P ∧ P ≤ H ∧ ¬ p ∣ P.relIndex H ∧
      H = P ⊔ T ∧ P ⊓ M = (frattini ↥P).map P.subtype := by
  have hTH : T ≤ H := h.isSylow.1
  have hMH : M ≤ H := h.maximal.le
  obtain ⟨p, hp, hp2, hsyl⟩ := sylow_structure h.subgroupOf hsolv
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p ↥H))
  obtain ⟨hsup, hinf⟩ := hsyl P₀ P₀.isPGroup' P₀.not_dvd_index
  set P := (P₀ : Subgroup ↥H).map H.subtype with hP
  have hPsub : P.subgroupOf H = P₀ :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  refine ⟨P, p, hp, hp2, P₀.isPGroup'.map H.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · show ¬ p ∣ (P.subgroupOf H).index
    rw [hPsub]
    exact P₀.not_dvd_index
  · have := congrArg (Subgroup.map H.subtype) hsup
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hTH, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at this
    exact this.symm
  · have h1 := congrArg (Subgroup.map H.subtype) hinf
    rw [Subgroup.map_inf _ _ _ H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hMH] at h1
    rw [h1, ← map_frattini_mulEquiv
      (Subgroup.equivMapOfInjective (P₀ : Subgroup ↥H) H.subtype H.subtype_injective),
      Subgroup.map_map, Subgroup.map_map]
    rfl

end Ambient

end Lem20B68

theorem lem12220_b68 (h331 : Stmt3_3_1) {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}
    (hH : Hyp1223 G T L V) (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hsolv : Group.IsSolvable ↥H) :
    ∃ (P : Subgroup G) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsPGroup p ↥P ∧ P ≤ H ∧ ¬ p ∣ P.relIndex H ∧
      H = P ⊔ T ∧ P ⊓ Subgroup.normalizer (L : Set G) = (frattini ↥P).map P.subtype := by
  obtain ⟨P, p, hp, hp2, hPp, hPH, hPi, hHPT, hΦ⟩ :=
    Lem20B68.exists_sylow_of_minParabolic (Lem7.minParabolic h331 hH hHs) hsolv
  refine ⟨P, p, hp, hp2, hPp, hPH, hPi, hHPT, ?_⟩
  rw [← hΦ, ← inf_assoc, inf_eq_left.mpr hPH]

@[expose] def Lem12220Choice : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P : Subgroup G) (p : ℕ), Hyp1223 G T L V →
    NoEscape12_2_13 L V → IsHStar T (Subgroup.normalizer (L : Set G)) H → Group.IsSolvable ↥H →
    p.Prime → p ≠ 2 → IsPGroup p ↥P → P ≤ H → ¬ p ∣ P.relIndex H → H = P ⊔ T →
    P ⊓ Subgroup.normalizer (L : Set G) = (frattini ↥P).map P.subtype →
      ∃ (U I : Subgroup G) (h : G), h ∈ P ∧ h ∉ Subgroup.normalizer (L : Set G) ∧
        I = V ⊔ CFSG.conjugate V h ∧ U = pCoreOf 2 I ∧
        U = (U ⊓ V) ⊔ (U ⊓ CFSG.conjugate V h) ∧ (U ⊓ V) ⊓ (U ⊓ CFSG.conjugate V h) = ⊥ ∧
        IsElemAbelian 2 U ∧ U = ⁅U, oTwoUpper I⁆ ∧
        (∃ _ : (U.subgroupOf I).Normal, Nonempty (↥I ⧸ U.subgroupOf I ≃* DihedralGroup p)) ∧
        (U ⊓ V).relIndex V = 2 ∧
        ∃ _ : IsMulCommutative ↥V, autOn U V = transvAxis ((U ⊓ V).subgroupOf V)

theorem lem12220PickFull_of (h331 : Stmt3_3_1) (hch : Lem12220Choice) : Lem12220PickFull := by
  intro G _ _ T L V H hH hNE hHs hsolv
  obtain ⟨P, p, hp, hp2, hPp, hPH, hPi, hHPT, hΦ⟩ := lem12220_b68 h331 hH hHs hsolv
  obtain ⟨U, I, h, hhP, hhM, hI, hU, hUdec, hUinf, hUe, hUc, hD, hidx, htr⟩ :=
    hch G T L V H P p hH hNE hHs hsolv hp hp2 hPp hPH hPi hHPT hΦ
  exact ⟨P, U, I, h, p, hHs, hsolv, hp, hp2, hPp, hPH, hPi, hHPT, hΦ, hhP, hhM, hI, hU, hUdec,
    hUinf, hUe, hUc, hD, hidx, htr⟩

end CFSG.Quasithin.H13
