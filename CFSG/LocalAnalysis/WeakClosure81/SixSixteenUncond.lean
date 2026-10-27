module

public import CFSG.LocalAnalysis.WeakClosure81.SixSixteen
public import CFSG.Quasithin.Background.E1SolvProduct
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusTools

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase
open Subgroup
open MulAction
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem eGen_le_centralizer_sup {V X S K : Subgroup G}
    (hV : IsElemAbelian 2 V) (hKXS : K = X ⊔ S) (hSK : IsSylowIn 2 S K)
    {i : ℕ} (hi : i + 1 < E3.sParam hV) :
    E1.eGen 1 K S (E3.gammaSet V i K) ≤
      (K ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G)) ⊔ S := by
  unfold E1.eGen
  refine iSup₂_le fun A hA => iSup_le fun hAS => iSup₂_le fun K₀ hK₀ => ?_
  have hAΓ : A ∈ E3.gammaSet V i S := ⟨hAS, hA.2⟩
  have hSK₀ : IsSylowIn 2 (S ⊓ K₀) K₀ := hK₀.2.2.1
  have hK₀eq : K₀ = (S ⊓ K₀) ⊔ twoResidual K₀ := (sup_twoResidual_eq hSK₀).symm
  have hcomm := E3.e3_19_comm hV hSK hi hAΓ hK₀
  have h2 : twoResidual K₀ ≤ K ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G) :=
    le_inf ((twoResidual_le K₀).trans hK₀.1)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm)
  rw [hK₀eq]
  exact sup_le (inf_le_left.trans le_sup_right) (h2.trans le_sup_left)

theorem exists_mul_of_sup {V X S K : Subgroup G} {p : ℕ}
    (hV : IsElemAbelian 2 V) (hp : p.Prime) (hp2 : p ≠ 2)
    (hKXS : K = X ⊔ S) (hXp : IsPGroup p X) (hS2 : IsPGroup 2 S)
    (hperm : (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G)) (hdisj : X ⊓ S = ⊥)
    (hSK : IsSylowIn 2 S K) {i : ℕ} (hi : i + 1 < E3.sParam hV) :
    ∀ g ∈ K,
      ∃ d ∈ K ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G),
      ∃ n ∈ K ⊓ Subgroup.normalizer (E3.wClos V i S : Set G), g = d * n := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  have hS_K : S ≤ K := by rw [hKXS]; exact le_sup_right
  have hcardNat : Nat.card K = Nat.card X * Nat.card S := by
    have hrel : S.relIndex K = Nat.card X := by
      rw [hKXS, CFSG.ABGTheoremB.TotallyInverted.Omnibus.relIndex_sup_of_mul_comm
        (A := X) (B := S) hperm]
      have h := Subgroup.relIndex_mul_card (H := S) (K := X)
      rw [inf_comm, hdisj, Subgroup.card_bot, mul_one] at h
      exact h
    have h := Subgroup.relIndex_mul_card (H := S) (K := K)
    rw [inf_eq_left.mpr hS_K, hrel] at h
    exact h.symm
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hXp
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hS2
  have hcardF : Fintype.card ↥K = p ^ a * 2 ^ b := by
    rw [← Nat.card_eq_fintype_card, hcardNat, ha, hb]
  have hSolv : Group.IsSolvable ↥K :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      hp Nat.prime_two hp2 hcardF
  have hwc : E1.weakClosure S (E3.gammaSet V i K) = E3.wClos V i S :=
    E3.weakClosure_gammaSet (V := V) (i := i) (hSH := hS_K)
  have hΩ : E1.IsInvColl K (E3.gammaSet V i K) := E3.isInvColl_gammaSet hV i K
  set D : Subgroup G := K ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G) with hDdef
  set N : Subgroup G := K ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) with hNdef
  have hE := eGen_le_centralizer_sup (V := V) (X := X) (S := S) (K := K) (i := i) hV hKXS hSK hi
  have hSc : S ≤ Subgroup.normalizer (E3.cClos V (i + 1) S : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_cClos (V := V) (i := i + 1) S)
  have hSw : S ≤ Subgroup.normalizer (E3.wClos V i S : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos (V := V) (i := i) S)
  have hSD : S ≤ Subgroup.normalizer (D : Set G) := by
    rw [hDdef]
    exact A1a.le_normalizer_inf (hS_K.trans Subgroup.le_normalizer)
      (A1a.le_normalizer_centralizer hSc)
  have hS_N : S ≤ N := by
    rw [hNdef]
    exact fun s hs => ⟨hS_K hs, hSw hs⟩
  have hDS : ((D ⊔ S : Subgroup G) : Set G) = (D : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left D S hSD
  have hSN' : (S : Set G) * (N : Set G) = (N : Set G) := by
    apply le_antisymm
    · rintro x ⟨s, hs, n, hn, rfl⟩
      exact N.mul_mem (hS_N hs) hn
    · intro n hn
      exact ⟨1, S.one_mem, n, hn, one_mul n⟩
  intro g hg
  obtain ⟨e, he, n, hn, hgn⟩ := E1.eGen_mul_normalizer_of_isSolvable_subgroup
    (K := K) (T := S) hS_K hSolv hSK hΩ ⟨g, hg⟩
  rw [hwc] at hn
  have hnN : n ∈ N := by rw [hNdef]; exact ⟨hn.2, hn.1⟩
  have heD : e ∈ (D ⊔ S : Subgroup G) := hE he
  have hmem : g ∈ ((D ⊔ S : Subgroup G) : Set G) * (N : Set G) := ⟨e, heD, n, hnN, hgn.symm⟩
  rw [hDS, mul_assoc, hSN'] at hmem
  rw [Set.mem_mul] at hmem
  obtain ⟨d, hd, n, hn, hdn⟩ := hmem
  refine ⟨d, ?_, n, ?_, hdn.symm⟩
  · simpa [hDdef] using hd
  · simpa [hNdef] using hn

theorem isPGroup_of_pow_eq_one {p : ℕ} {X : Subgroup G} (hexp : ∀ x ∈ X, x ^ p = 1) :
    IsPGroup p X :=
  IsPGroup.of_exponent_dvd_pow (n := 1)
    (by
      rw [pow_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun x : ↥X => Subtype.ext (by simpa using hexp x x.2)))

theorem isPretransitive_of_coprime_index {D Ω : Type*} [Group D] [Finite D] [MulAction D Ω]
    [Finite Ω] (P : Subgroup D) (htrans : IsPretransitive D Ω)
    (hcop : Nat.Coprime (Nat.card Ω) P.index) :
    letI : MulAction P Ω := MulAction.compHom Ω P.subtype
    IsPretransitive P Ω := by
  letI : MulAction P Ω := MulAction.compHom Ω P.subtype
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact ⟨fun x => isEmptyElim x⟩
  · obtain ⟨ω⟩ := hΩ
    haveI : IsPretransitive D Ω := htrans
    rw [isPretransitive_iff_base (G := ↥P) ω]
    intro x
    have hDcard : (MulAction.stabilizer D ω).index = Nat.card Ω :=
      MulAction.index_stabilizer_of_transitive D ω
    have hmap : (MulAction.stabilizer P ω).map P.subtype =
        P ⊓ MulAction.stabilizer D ω := by
      ext d
      simp only [Subgroup.mem_map, Subgroup.mem_inf]
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.2, hp⟩
      · rintro ⟨hdP, hdω⟩
        exact ⟨⟨d, hdP⟩, hdω, rfl⟩
    have hidx : (MulAction.stabilizer P ω).index * P.index =
        (P ⊓ MulAction.stabilizer D ω).relIndex (MulAction.stabilizer D ω) *
          (MulAction.stabilizer D ω).index := by
      rw [← Subgroup.index_map_subtype (H := P) (MulAction.stabilizer P ω), hmap,
        ← Subgroup.relIndex_mul_index (show P ⊓ MulAction.stabilizer D ω ≤
          MulAction.stabilizer D ω from inf_le_right)]
    have hdvd : Nat.card Ω ∣ (MulAction.stabilizer P ω).index := by
      apply hcop.dvd_of_dvd_mul_right
      rw [hidx, hDcard]
      exact dvd_mul_left _ _
    have hpos : 0 < (MulAction.stabilizer P ω).index := by
      rw [MulAction.index_stabilizer]
      exact (Set.ncard_pos (s := MulAction.orbit P ω)).mpr ⟨ω, MulAction.mem_orbit_self ω⟩
    have hle : (MulAction.stabilizer P ω).index ≤ Nat.card Ω := by
      rw [MulAction.index_stabilizer]
      calc (MulAction.orbit P ω).ncard ≤ (Set.univ : Set Ω).ncard :=
            Set.ncard_le_ncard (Set.subset_univ _)
        _ = Nat.card Ω := Set.ncard_univ Ω
    have heq : (MulAction.stabilizer P ω).index = Nat.card Ω :=
      le_antisymm hle (Nat.le_of_dvd hpos hdvd)
    have huniv : MulAction.orbit P ω = Set.univ :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
        (by rw [Set.ncard_univ, ← MulAction.index_stabilizer, heq])
    exact MulAction.mem_orbit_iff.mp (huniv ▸ Set.mem_univ x)

theorem isSylowIn_sup_of_mul_comm {X S : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hXp : IsPGroup p X) (hS2 : IsPGroup 2 S)
    (hperm : (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G)) :
    IsSylowIn 2 S (X ⊔ S) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdisj : X ⊓ S = ⊥ := by
    have hd := IsPGroup.disjoint_of_ne p 2 hp2 X S hXp hS2
    rwa [disjoint_iff] at hd
  refine ⟨le_sup_right, hS2, ?_⟩
  have hrel : S.relIndex (X ⊔ S) = Nat.card X := by
    rw [CFSG.ABGTheoremB.TotallyInverted.Omnibus.relIndex_sup_of_mul_comm (A := X) (B := S) hperm]
    have h := Subgroup.relIndex_mul_card (H := S) (K := X)
    rw [inf_comm, hdisj, Subgroup.card_bot, mul_one] at h
    exact h
  rw [hrel]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hXp
  rw [ha]
  intro h2dvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd)).symm

theorem relIndex_inf_dvd_card_of_mul_comm {X S D K : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hKXS : K = X ⊔ S) (hperm : (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G))
    (hXp : IsPGroup p X) (hS2 : IsPGroup 2 S)
    (hDK : D ≤ K) (hSD : S ≤ Subgroup.normalizer (D : Set G)) :
    (D ⊓ X).relIndex D ∣ Nat.card S := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXK : X ≤ K := by rw [hKXS]; exact le_sup_left
  have hSK : S ≤ K := by rw [hKXS]; exact le_sup_right
  have hKmul : (K : Set G) = (X : Set G) * (S : Set G) := by
    rw [hKXS]
    exact CFSG.ABGTheoremB.TotallyInverted.Omnibus.coe_sup_of_mul_comm hperm
  have hdisj : X ⊓ S = ⊥ := by
    have hd := IsPGroup.disjoint_of_ne p 2 hp2 X S hXp hS2
    rwa [disjoint_iff] at hd
  set DS : Subgroup G := D ⊔ S with hDSdef
  have hDDS : D ≤ DS := le_sup_left
  have hSDS : S ≤ DS := le_sup_right
  have hDDSK : DS ≤ K := sup_le hDK hSK
  haveI hDnormDS : (D.subgroupOf DS).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := DS) (N := D)
      (sup_le Subgroup.le_normalizer hSD)
  have hDSX : (DS : Set G) = (X ⊓ DS : Set G) * (S : Set G) := by
    apply Set.Subset.antisymm
    · intro g hg
      have hgK : g ∈ (K : Set G) := hDDSK hg
      rw [hKmul] at hgK
      obtain ⟨x, hx, s, hs, hxs⟩ := hgK
      refine ⟨x, ⟨hx, ?_⟩, s, hs, hxs⟩
      have hxeq : x = g * s⁻¹ := by rw [← hxs]; group
      rw [hxeq]
      exact DS.mul_mem hg (hSDS (S.inv_mem hs))
    · rintro g ⟨y, hy, s, hs, hys⟩
      rw [← hys]
      exact DS.mul_mem hy.2 (hSDS hs)
  have hDrelS : D.relIndex DS = D.relIndex S := by
    have hcomm : (S : Set G) * (D : Set G) = (D : Set G) * (S : Set G) :=
      Subgroup.set_mul_normalizer_comm (S : Set G) D hSD
    have h := CFSG.ABGTheoremB.TotallyInverted.Omnibus.relIndex_sup_of_mul_comm
      (A := S) (B := D) hcomm
    rwa [sup_comm] at h
  have hDS2 : IsPGroup 2 (DS ⧸ D.subgroupOf DS) := by
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hS2
    refine IsPGroup.of_card_dvd_pow (n := b) ?_
    rw [← Subgroup.index_eq_card,
      show (D.subgroupOf DS).index = D.relIndex DS from rfl, hDrelS]
    exact ⟨Nat.card ↥(D ⊓ S), ((Subgroup.relIndex_mul_card (H := D) (K := S)).trans hb).symm⟩
  have hleD : X ⊓ DS ≤ D := by
    set Q : Subgroup (DS ⧸ D.subgroupOf DS) :=
      ((X ⊓ DS).subgroupOf DS).map (QuotientGroup.mk' (D.subgroupOf DS)) with hQdef
    have hQp : IsPGroup p Q := by
      rw [hQdef]
      exact ((hXp.to_le inf_le_left).of_equiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : X ⊓ DS ≤ DS)).symm).map
          (QuotientGroup.mk' (D.subgroupOf DS))
    have hQ2 : IsPGroup 2 Q := hDS2.of_injective Q.subtype Q.subtype_injective
    have hQbot : Q = ⊥ := by
      simpa using (disjoint_iff.mp (IsPGroup.disjoint_of_ne p 2 hp2 Q Q hQp hQ2))
    have hmk : ((X ⊓ DS).subgroupOf DS).map (QuotientGroup.mk' (D.subgroupOf DS)) = ⊥ := by
      rw [← hQdef]; exact hQbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmk
    intro y hy
    have hyDS : y ∈ DS := hy.2
    have hmem : (⟨y, hyDS⟩ : ↥DS) ∈ (X ⊓ DS).subgroupOf DS := hy
    have := hmk hmem
    rwa [Subgroup.mem_subgroupOf] at this
  have hXDS : X ⊓ DS = D ⊓ X := by
    apply le_antisymm
    · intro y hy
      exact ⟨hleD hy, hy.1⟩
    · intro y hy
      exact ⟨hy.2, hDDS hy.1⟩
  have hcardDS : Nat.card DS = Nat.card ↥(D ⊓ X) * Nat.card S := by
    have hdisjX : Disjoint (X ⊓ DS) S := by
      rw [disjoint_iff]
      exact le_bot_iff.1
        ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans (le_of_eq hdisj))
    have hcardX : Nat.card DS = Nat.card ↥(X ⊓ DS) * Nat.card S := by
      let f : ↥(X ⊓ DS) × ↥S → ↥DS := fun z =>
        ⟨(z.1 : G) * (z.2 : G), DS.mul_mem z.1.2.2 (hSDS z.2.2)⟩
      have hf_inj : Function.Injective f := by
        intro x y hxy
        have h : (x.1 : G) * (x.2 : G) = (y.1 : G) * (y.2 : G) := congrArg Subtype.val hxy
        exact Subgroup.mul_injective_of_disjoint hdisjX h
      have hf_surj : Function.Surjective f := by
        intro z
        have hz : (z : G) ∈ (X ⊓ DS : Set G) * (S : Set G) := by
          rw [← hDSX]; exact z.2
        obtain ⟨y, hy, s, hs, hys⟩ := hz
        exact ⟨(⟨y, hy⟩, ⟨s, hs⟩), Subtype.ext hys⟩
      calc Nat.card DS = Nat.card (↥(X ⊓ DS) × ↥S) :=
            Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm
        _ = Nat.card ↥(X ⊓ DS) * Nat.card ↥S := Nat.card_prod _ _
    rw [hcardX, hXDS]
  have hrelDS : (D ⊓ X).relIndex DS = Nat.card S := by
    have h := Subgroup.relIndex_mul_card (H := D ⊓ X) (K := DS)
    rw [inf_eq_left.mpr (inf_le_left.trans hDDS), hcardDS,
      mul_comm (Nat.card ↥(D ⊓ X)) (Nat.card S)] at h
    exact Nat.mul_right_cancel Nat.card_pos h
  have hrelD : (D ⊓ X).relIndex D * D.relIndex DS = Nat.card S := by
    rw [Subgroup.relIndex_mul_relIndex (D ⊓ X) D DS inf_le_left hDDS, hrelDS]
  exact ⟨D.relIndex DS, hrelD.symm⟩

theorem six_sixteen_A {X S K D W : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hKXS : K = X ⊔ S) (hperm : (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G))
    (hXp : IsPGroup p X) (hS2 : IsPGroup 2 S)
    (hDK : D ≤ K) (hSD : S ≤ Subgroup.normalizer (D : Set G))
    (hSW : S ≤ Subgroup.normalizer (W : Set G))
    (hfac : ∀ g ∈ K, ∃ d ∈ D, ∃ n ∈ K ⊓ Subgroup.normalizer (W : Set G), g = d * n) :
    ∀ x ∈ X, ∃ n ∈ X ⊓ Subgroup.normalizer (W : Set G), ∃ d ∈ X ⊓ D, x = n * d := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype G := Fintype.ofFinite G
  letI : MulAction G (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj : G →* MulAut G)
  have hXK : X ≤ K := by rw [hKXS]; exact le_sup_left
  have hSK : S ≤ K := by rw [hKXS]; exact le_sup_right
  have hKmul : (K : Set G) = (X : Set G) * (S : Set G) := by
    rw [hKXS]
    exact CFSG.ABGTheoremB.TotallyInverted.Omnibus.coe_sup_of_mul_comm hperm
  have hstab : ∀ g : G, g • W = W ↔ g ∈ Subgroup.normalizer (W : Set G) := by
    intro g
    change W.map (MulAut.conj g).toMonoidHom = W ↔ g ∈ Subgroup.normalizer (W : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rfl
  letI : MulAction ↥K (Subgroup G) := MulAction.compHom (Subgroup G) K.subtype
  letI : MulAction ↥X (MulAction.orbit K W) :=
    MulAction.compHom (MulAction.orbit K W) (Subgroup.inclusion hXK)
  letI : MulAction ↥D (MulAction.orbit K W) :=
    MulAction.compHom (MulAction.orbit K W) (Subgroup.inclusion hDK)
  haveI : Finite (MulAction.orbit K W) :=
    Finite.of_surjective
      (fun k : ↥K => (⟨k • W, MulAction.mem_orbit W k⟩ : MulAction.orbit K W))
      (by rintro ⟨ω, hω⟩; rcases hω with ⟨k, rfl⟩; exact ⟨k, rfl⟩)
  have hXtrans : IsPretransitive ↥X (MulAction.orbit K W) := by
    rw [isPretransitive_iff_base (G := ↥X)
      (⟨W, MulAction.mem_orbit_self W⟩ : MulAction.orbit K W)]
    rintro ⟨ω, hω⟩
    rcases hω with ⟨k, rfl⟩
    have hk : (k : G) ∈ (X : Set G) * (S : Set G) := hKmul ▸ k.2
    rcases hk with ⟨x, hx, s, hs, hxs⟩
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change (Subgroup.inclusion hXK ⟨x, hx⟩ : ↥K) • W = k • W
    change x • W = (k : G) • W
    rw [← hxs, mul_smul, (hstab s).2 (hSW hs)]
  have hDtrans : IsPretransitive ↥D (MulAction.orbit K W) := by
    rw [isPretransitive_iff_base (G := ↥D)
      (⟨W, MulAction.mem_orbit_self W⟩ : MulAction.orbit K W)]
    rintro ⟨ω, hω⟩
    rcases hω with ⟨k, rfl⟩
    obtain ⟨d, hd, n, hn, hdn⟩ := hfac (k : G) k.2
    refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
    change (Subgroup.inclusion hDK ⟨d, hd⟩ : ↥K) • W = k • W
    change d • W = (k : G) • W
    rw [hdn, mul_smul, (hstab n).2 hn.2]
  haveI : IsPretransitive ↥X (MulAction.orbit K W) := hXtrans
  obtain ⟨n, hn⟩ : ∃ n, Nat.card (MulAction.orbit K W) = p ^ n := by
    obtain ⟨n, hn⟩ := IsPGroup.card_orbit (p := p) (G := ↥X) (α := MulAction.orbit K W)
      hXp (⟨W, MulAction.mem_orbit_self W⟩ : MulAction.orbit K W)
    have huniv : (MulAction.orbit ↥X
        (⟨W, MulAction.mem_orbit_self W⟩ : MulAction.orbit K W) : Set (MulAction.orbit K W)) =
        Set.univ := MulAction.orbit_eq_univ (↥X) _
    have hcard : Nat.card (MulAction.orbit ↥X
        (⟨W, MulAction.mem_orbit_self W⟩ : MulAction.orbit K W)) =
        Nat.card (MulAction.orbit K W) := by
      rw [Nat.card_coe_set_eq (MulAction.orbit ↥X
            (⟨W, MulAction.mem_orbit_self W⟩ : MulAction.orbit K W)),
        Nat.card_coe_set_eq (MulAction.orbit K W), huniv, Set.ncard_univ,
        Nat.card_coe_set_eq (MulAction.orbit K W)]
    exact ⟨n, by rw [← hcard]; exact hn⟩
  have hcop : Nat.Coprime (Nat.card (MulAction.orbit K W))
      ((D ⊓ X).subgroupOf D).index := by
    have hidx2 : ((D ⊓ X).subgroupOf D).index = (D ⊓ X).relIndex D := rfl
    rw [hn, hidx2]
    apply Nat.Coprime.pow_left
    rw [hp.coprime_iff_not_dvd]
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hS2
    have hdvd : (D ⊓ X).relIndex D ∣ 2 ^ b := by
      rw [← hb]
      exact relIndex_inf_dvd_card_of_mul_comm hp hp2 hKXS hperm hXp hS2 hDK hSD
    intro hpdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (hpdvd.trans hdvd)))
  have hPtrans := isPretransitive_of_coprime_index (D := ↥D)
    (Ω := MulAction.orbit K W) ((D ⊓ X).subgroupOf D) hDtrans hcop
  letI : MulAction ↥((D ⊓ X).subgroupOf D) (MulAction.orbit K W) :=
    MulAction.compHom (MulAction.orbit K W) ((D ⊓ X).subgroupOf D).subtype
  haveI : IsPretransitive ↥((D ⊓ X).subgroupOf D) (MulAction.orbit K W) := hPtrans
  intro x hx
  have hxK : x⁻¹ ∈ K := hXK (X.inv_mem hx)
  have hmem : x⁻¹ • W ∈ MulAction.orbit K W :=
    MulAction.mem_orbit W (⟨x⁻¹, hxK⟩ : ↥K)
  obtain ⟨q, hq⟩ :=
    (inferInstance : IsPretransitive ↥((D ⊓ X).subgroupOf D) (MulAction.orbit K W)).exists_smul_eq
      (⟨W, MulAction.mem_orbit_self W⟩ : MulAction.orbit K W) ⟨x⁻¹ • W, hmem⟩
  let qG : G := (q.1 : G)
  have hqW : qG • W = x⁻¹ • W := by
    change (q • (⟨W, MulAction.mem_orbit_self W⟩ : MulAction.orbit K W) : Subgroup G) = x⁻¹ • W
    exact congrArg Subtype.val hq
  have hqD : qG ∈ D := q.1.2
  have hqX : qG ∈ X := by
    have h : q.1 ∈ (D ⊓ X).subgroupOf D := q.2
    rw [Subgroup.mem_subgroupOf] at h
    exact h.2
  refine ⟨x * qG, ⟨X.mul_mem hx hqX, ?_⟩,
    qG⁻¹, ⟨X.inv_mem hqX, D.inv_mem hqD⟩, by group⟩
  exact (hstab (x * qG)).1 (by rw [mul_smul, hqW, ← mul_smul, mul_inv_cancel, one_smul])

theorem exists_mul_of_isPGroup {V X S : Subgroup G} {p : ℕ}
    (hV : IsElemAbelian 2 V) (hp : p.Prime) (hp2 : p ≠ 2)
    (hXp : IsPGroup p X) (hS2 : IsPGroup 2 S)
    (hperm : (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G))
    {i : ℕ} (hi : i + 1 < E3.sParam hV) :
    ∀ x ∈ X, ∃ a ∈ X ⊓ Subgroup.normalizer (E3.wClos V i S : Set G),
      ∃ b ∈ X ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G), x = a * b := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSXS : IsSylowIn 2 S (X ⊔ S) := isSylowIn_sup_of_mul_comm hp hp2 hXp hS2 hperm
  have hdisj : X ⊓ S = ⊥ := by
    have hd := IsPGroup.disjoint_of_ne p 2 hp2 X S hXp hS2
    rwa [disjoint_iff] at hd
  have hfac := exists_mul_of_sup (V := V) (X := X) (S := S) (K := X ⊔ S) (p := p)
    hV hp hp2 rfl hXp hS2 hperm hdisj hSXS hi
  have hS_K : S ≤ X ⊔ S := le_sup_right
  have hSc : S ≤ Subgroup.normalizer (E3.cClos V (i + 1) S : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_cClos (V := V) (i := i + 1) S)
  have hSD : S ≤ Subgroup.normalizer
      ↑((X ⊔ S) ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G)) :=
    A1a.le_normalizer_inf (hS_K.trans Subgroup.le_normalizer) (A1a.le_normalizer_centralizer hSc)
  have hSW : S ≤ Subgroup.normalizer (E3.wClos V i S : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos (V := V) (i := i) S)
  have hA := six_sixteen_A (X := X) (S := S) (K := X ⊔ S)
    (D := (X ⊔ S) ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G))
    (W := E3.wClos V i S) hp hp2 rfl hperm hXp hS2 inf_le_left hSD hSW hfac
  intro x hx
  obtain ⟨n, hn, d, hd, rfl⟩ := hA x hx
  exact ⟨n, hn, d, ⟨hd.1, hd.2.2⟩, rfl⟩

theorem six_sixteen_one_i_uncond {V M H S X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : rankThreeIsMaxTwoLocal M) (hS : IsSylowIn 2 S H) {k : ℕ} (hk : 1 ≤ k)
    (hH : E1.InE k H) (hW0 : E3.wClos V 0 S ≠ ⊥) (hgt : k + 1 < E3.sParam hV)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hXM : X ≤ M)
    (hexp : ∀ x ∈ X, x ^ p = 1) (hbig : p ^ 2 < Nat.card X)
    (hperm : (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G))
    (hUY : ∀ Y : Subgroup G, Y ≤ X → ¬ IsCyclic Y → InCalU M Y) :
    H ≤ M := by
  have hXp : IsPGroup p X := isPGroup_of_pow_eq_one hexp
  refine six_sixteen_one_i hV hM hS hk hH hW0 hgt hp hXM hexp hbig hUY ?_
  intro i hi x hx
  exact exists_mul_of_isPGroup (V := V) (X := X) (S := S) (p := p)
    hV hp hp2 hXp hS.isPGroup hperm (i := i) (by omega) x hx

theorem six_sixteen_one_iii_uncond {V M H S X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : rankThreeIsMaxTwoLocal M) (hS : IsSylowIn 2 S H) {k : ℕ} (hk : 1 ≤ k)
    (hH : E1.InE k H) (hW0 : E3.wClos V 0 S ≠ ⊥) (hgt : k + 1 < E3.sParam hV)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hXp : IsPGroup p X)
    (hXM : X ≤ M) (hXnc : ¬ IsCyclic X)
    (hIrr : UC22.IrrOn (Subgroup.normalizer (X : Set G) ⊓
        Subgroup.normalizer (S : Set G)) X)
    (hperm : (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G))
    (hUY : ∀ Y : Subgroup G, Y ≤ X → ¬ IsCyclic Y → InCalU M Y) :
    H ≤ M := by
  refine six_sixteen_one_iii hV hM hS hk hH hW0 hgt hXM hXnc hIrr hUY ?_
  intro i hi x hx
  exact exists_mul_of_isPGroup (V := V) (X := X) (S := S) (p := p)
    hV hp hp2 hXp hS.isPGroup hperm (i := i) (by omega) x hx

theorem six_sixteen_two_uncond {V M H S X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : rankThreeIsMaxTwoLocal M) (hS : IsSylowIn 2 S H) {k : ℕ} (hk : 1 ≤ k)
    (hH : E1.InE k H) (hW0 : E3.wClos V 0 S ≠ ⊥) (hgt : k + 2 < E3.sParam hV)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hXM : X ≤ M) (hXnc : ¬ IsCyclic X)
    (hexp : ∀ x ∈ X, x ^ p = 1)
    (hperm : (X : Set G) * (S : Set G) = (S : Set G) * (X : Set G))
    (hUY : ∀ Y : Subgroup G, Y ≤ X → ¬ IsCyclic Y → InCalU M Y) :
    H ≤ M := by
  have hXp : IsPGroup p X := isPGroup_of_pow_eq_one hexp
  refine six_sixteen_two hV hM hS hk hH hW0 hgt hp hXM hXnc hexp hUY ?_
  intro i hi x hx
  exact exists_mul_of_isPGroup (V := V) (X := X) (S := S) (p := p)
    hV hp hp2 hXp hS.isPGroup hperm (i := i) (by omega) x hx

end CFSG.LocalAnalysis.WeakClosure81
