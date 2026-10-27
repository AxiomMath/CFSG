module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfWeylCtx

private lemma commutator_eq_self_of_isQuasisimple {Q : Type*} [Group Q] {A : Subgroup Q}
    (h : CFSG.Assembly.IsQuasisimple A) : ⁅A, A⁆ = A := by
  have h1 : (commutator A).map A.subtype = ⁅A, A⁆ := Subgroup.map_subtype_commutator A
  rw [h.1, Subgroup.map_top, Subgroup.range_subtype] at h1
  exact h1.symm

private lemma map_commutator_subgroupOf_eq {G : Type*} [Group G] {X K : Subgroup G} (hKX : K ≤ X)
    {Q : Type*} [Group Q] (π : X →* Q) :
    ((⁅K, K⁆).subgroupOf X).map π = ⁅(K.subgroupOf X).map π, (K.subgroupOf X).map π⁆ := by
  have h : (⁅K, K⁆).subgroupOf X = ⁅K.subgroupOf X, K.subgroupOf X⁆ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKX,
      Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_mono hKX hKX).trans
        (Subgroup.commutator_le_self X))]
  rw [h, Subgroup.map_commutator]

private lemma commutator_eq_top_of_pComponent {G : Type*} [Group G] {p : ℕ} {X K : Subgroup G}
    (hpc : LargeEvenPComponent p X K) : commutator K = ⊤ := by
  have hmain : (commutator K).map K.subtype = K := by
    rw [Subgroup.map_subtype_commutator K]
    refine le_antisymm (Subgroup.commutator_le_self K) ?_
    by_contra hle
    have hlt : ⁅K, K⁆ < K :=
      lt_of_le_of_ne (Subgroup.commutator_le_self K) (fun h => hle (le_of_eq h.symm))
    have hnorm : (⁅K, K⁆).subgroupOf K = commutator K := by
      rw [← Subgroup.map_subtype_commutator K]
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    have hsn : CFSG.Assembly.IsSubnormal ⁅K, K⁆ X :=
      CFSG.Assembly.IsSubnormal.step (Subgroup.commutator_le_self K)
        (by rw [hnorm]; infer_instance) hpc.2.1
    have hperf : ⁅(K.subgroupOf X).map (QuotientGroup.mk' (LargeEvenPPrimeCore p X)),
        (K.subgroupOf X).map (QuotientGroup.mk' (LargeEvenPPrimeCore p X))⁆ =
        (K.subgroupOf X).map (QuotientGroup.mk' (LargeEvenPPrimeCore p X)) :=
      commutator_eq_self_of_isQuasisimple hpc.2.2.1.2.2
    have heq : ((⁅K, K⁆).subgroupOf X).map (QuotientGroup.mk' (LargeEvenPPrimeCore p X)) =
        (K.subgroupOf X).map (QuotientGroup.mk' (LargeEvenPPrimeCore p X)) := by
      rw [map_commutator_subgroupOf_eq hpc.1 (QuotientGroup.mk' (LargeEvenPPrimeCore p X)),
        hperf]
    exact (hpc.2.2.2 ⁅K, K⁆ hlt hsn) heq
  apply Subgroup.map_injective K.subtype_injective
  rw [hmain, Subgroup.map_top, Subgroup.range_subtype]

private lemma centralizer_pair_eq {G : Type*} [Group G] (a b : G) :
    Subgroup.centralizer ({a, b} : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨fun t ht => h t (Or.inl ht), fun t ht => h t (Or.inr ht)⟩
  · rintro ⟨ha, hb⟩ z hz
    rcases hz with rfl | rfl
    · exact ha _ rfl
    · exact hb _ rfl

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  (h : GGHalfWeylCtx p B Bs x L D J m y K)

include h

theorem basic :
    (∀ b ∈ Bs, ∀ c ∈ Bs, b * c = c * b) ∧ (∀ b ∈ Bs, b ^ 3 = 1) ∧ x ∈ Bs ∧ y ∈ Bs ∧
    x ≠ 1 ∧ y ≠ 1 ∧ (∀ l ∈ L, x * l = l * x) ∧ (∀ k ∈ K, y * k = k * y) ∧
    (¬ ∀ k ∈ K, x * k = k * x) ∧
    (∀ g ∈ Bs, (∀ l ∈ L, g * l = l * g) → g ∈ Subgroup.zpowers x) := by
  obtain ⟨hI, hBs, hDJ⟩ := h.cfg
  obtain ⟨-, hp3, -, -, hnbr, -, -⟩ := h.nbr
  subst hp3
  have hSstar := hI.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb c hc
    exact congrArg Subtype.val (hBs.2.1.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  · exact hBs.2.1.2
  · exact hBs.1 hSstar.2.1
  · exact hBs.1 hnbr.1.2.1
  · exact hSstar.2.2.1
  · exact hnbr.1.2.2.1
  · intro l hl
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hSstar.2.2.2.1.1 hl)).symm
  · intro k hk
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hnbr.1.2.2.2.1 hk)).symm
  · intro hcomm
    apply hnbr.2.2.2
    have hbot : (⁅K, Subgroup.zpowers x⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hcomm k hk).symm
    rw [hbot]
    exact bot_le
  · have hp : Nat.Prime 3 := hI.2.2.2.2.2.1.1
    have hxne : x ≠ 1 := hSstar.2.2.1
    have hxBs : x ∈ Bs := hBs.1 hSstar.2.1
    have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSstar.2.2.2.1.1
    have hxpow : x ^ 3 = 1 := hBs.2.1.2 x hxBs
    have hxord : orderOf x = 3 := by
      have : Fact (Nat.Prime 3) := ⟨hp⟩
      exact orderOf_eq_prime hxpow hxne
    intro g hg hgc
    let S : Subgroup G := Bs ⊓ Subgroup.centralizer (L : Set G)
    have hxS : x ∈ S := ⟨hxBs, Subgroup.mem_centralizer_iff.mpr (fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLx hl))⟩
    have hgS : g ∈ S := ⟨hg, Subgroup.mem_centralizer_iff.mpr (fun l hl =>
      (hgc l hl).symm)⟩
    have hSp : IsPGroup 3 ↥S := fun s => ⟨1, by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
      exact hBs.2.1.2 (s : G) s.2.1⟩
    have hScyc : IsCyclic ↥S := hSstar.2.2.2.2 S inf_le_right hSp
    obtain ⟨s, hs⟩ := hScyc.exists_generator
    have hmap : (Subgroup.zpowers s).map S.subtype = Subgroup.zpowers (s : G) :=
      MonoidHom.map_zpowers S.subtype s
    have hSeq : S = Subgroup.zpowers (s : G) := by
      apply le_antisymm
      · intro z hz
        have hz' : z ∈ (Subgroup.zpowers s).map S.subtype :=
          ⟨⟨z, hz⟩, hs ⟨z, hz⟩, rfl⟩
        rwa [hmap] at hz'
      · rw [Subgroup.zpowers_le]
        exact s.2
    have hs_pow : s ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      exact hBs.2.1.2 (s : G) s.2.1
    have hsord_dvd : orderOf s ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hs_pow
    have hsord : orderOf s = 3 := by
      rcases (Nat.dvd_prime hp).mp hsord_dvd with h1 | hp'
      · exfalso
        have hs1 : s = 1 := orderOf_eq_one_iff.mp h1
        have hxmem : (⟨x, hxS⟩ : S) ∈ Subgroup.zpowers s := hs ⟨x, hxS⟩
        rw [hs1] at hxmem
        have hxe : (⟨x, hxS⟩ : S) = 1 := by simpa using hxmem
        exact hxne (Subtype.ext_iff.mp hxe)
      · exact hp'
    have hcardS : Nat.card S = 3 := by
      have hord : orderOf (s : G) = orderOf s :=
        orderOf_injective S.subtype Subtype.coe_injective s
      rw [hSeq, Nat.card_zpowers, hord, hsord]
    have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, hxord]
    have hzxle : Subgroup.zpowers x ≤ S := Subgroup.zpowers_le.mpr hxS
    have heq : Subgroup.zpowers x = S :=
      Subgroup.eq_of_le_of_card_ge hzxle (by rw [hcardS, hcardx])
    rw [heq]
    exact hgS

theorem p_eq : p = 3 := h.nbr.2.1

theorem five_le : 5 ≤ m + 1 + 1 := h.nbr.2.2.1

theorem perfect_L : commutator L = ⊤ := by
  obtain ⟨hI, -, -⟩ := h.cfg
  exact hI.2.2.2.2.2.2.1.2.2.2.1.2.2.1

theorem perfect_K : commutator K = ⊤ := by
  obtain ⟨-, -, -, -, hnbr, -, -⟩ := h.nbr
  exact commutator_eq_top_of_pComponent hnbr.1.2.2.2.2.1

theorem component_J : IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨-, -, hDJ⟩ := h.cfg
  obtain ⟨-, -, -, -, hnbr, -, -⟩ := h.nbr
  obtain ⟨-, -, -, -, -, -, hLx, -, -, -⟩ := h.basic
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hDJ.1.2.2.2.2.2.1
  have hLCx : L ≤ Subgroup.centralizer ({x} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hLx l hl).symm
  have hmain : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hnbr.2.1, Subgroup.centralizer_closure, centralizer_pair_eq x y, ← inf_assoc,
      inf_eq_left.mpr hLCx]
  rw [hmain] at hcomp
  exact hcomp

theorem not_centralizes_L : ¬ ∀ l ∈ L, y * l = l * y := by
  intro hc
  obtain ⟨-, hpow, hxBs, hyBs, hxne, hyne, -, hKy, hxK, hCL⟩ := h.basic
  have hy_zx : y ∈ Subgroup.zpowers x := hCL y hyBs hc
  have hxord : orderOf x = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime (hpow x hxBs) hxne
  have hyord : orderOf y = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime (hpow y hyBs) hyne
  have heq : Subgroup.zpowers y = Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy_zx) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hyord]
  have hx_y : x ∈ Subgroup.zpowers y := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  apply hxK
  intro k hk
  have hkC : y ∈ Subgroup.centralizer ({k} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hKy k hk)
  have hxC : x ∈ Subgroup.centralizer ({k} : Set G) :=
    (Subgroup.zpowers_le.mpr hkC) hx_y
  exact Subgroup.mem_centralizer_singleton_iff.mp hxC

theorem normalizer_L : Bs ≤ Subgroup.normalizer (L : Set G) :=
  GGDichotomy.le_normalizer_of_innerDiagOn h.inn.1

theorem normalizer_K : Bs ≤ Subgroup.normalizer (K : Set G) :=
  GGDichotomy.le_normalizer_of_innerDiagOn (h.inn.2 y K h.nbr.2.2.2.2.1)

theorem exists_frames (hstep1 : ∀ {G : Type} [Group G] [Finite G] {B Bs X : Subgroup G} {p : ℕ}, p =
    3 → GGBstar p B Bs → ∀ {N : ℕ}, 5 ≤ N + 1 → Bs ≤ Subgroup.normalizer (X : Set G) → ∀ φ :
    SpecialLinearGroup (Fin (N + 1)) F2 →* G, φ.range = X → Function.Injective φ → ∃ A :
    SpecialLinearGroup (Fin (N + 1)) F2, GGHalfTorusFrame Bs X (halfTorus N) (φ.comp (MulAut.conj
    A).toMonoidHom)) :
    ∃ ψL ψK : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G,
      GGHalfTorusFrame Bs L (halfTorus (m + 1 + 1)) ψL ∧
      GGHalfTorusFrame Bs K (halfTorus (m + 1 + 1)) ψK := by
  obtain ⟨hI, hBs, hDJ⟩ := h.cfg
  obtain ⟨hmodL, hp3, hn, -, hnbr, hmodK, -⟩ := h.nbr
  have hm : 2 ≤ m := by omega
  obtain ⟨φL, hφL, hinjL⟩ := exists_slLift_two hm h.perfect_L hmodL
  obtain ⟨φK, hφK, hinjK⟩ := exists_slLift_two hm h.perfect_K hmodK
  obtain ⟨AL, hAL⟩ := hstep1 hp3 hBs (N := m + 1 + 1) (by omega) h.normalizer_L φL hφL hinjL
  obtain ⟨AK, hAK⟩ := hstep1 hp3 hBs (N := m + 1 + 1) (by omega) h.normalizer_K φK hφK hinjK
  exact ⟨_, _, hAL, hAK⟩

end GGHalfWeylCtx

end CFSG.StandardType

end
