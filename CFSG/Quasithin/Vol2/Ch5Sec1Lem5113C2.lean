module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Steps
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2Two
public import CFSG.Quasithin.Vol2.Ch1Eight

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

@[expose] def FactC2Hall : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Q₁ Q₂ R₁ R₂ S B D : Subgroup A) (s : A),
    (IsSporadic .J1 ↥Q₁ ∨
      ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 ↥Q₁) →
    s ∈ S → Q₂ = Q₁.map (MulAut.conj s).toMonoidHom → R₂ = R₁.map (MulAut.conj s).toMonoidHom →
    ⁅Q₁, Q₂⁆ = ⊥ → Q₁ ⊓ Q₂ = ⊥ → IsPGroup 2 ↥S →
    S ≤ Subgroup.normalizer ((Q₁ ⊔ Q₂ : Subgroup A) : Set A) →
    IsSylowTwoOf (S ⊓ (Q₁ ⊔ Q₂)) (Q₁ ⊔ Q₂) →
    R₁ ≤ Q₁ → ⁅R₁, R₁⁆ = R₁ → LieModel (ModO2 R₁) .PSL 2 2 2 →
    IsSylowTwoOf (S ⊓ (R₁ ⊔ R₂)) (R₁ ⊔ R₂) →
    Lin2.IsHallTwoPrimeOf B
      ((R₁ ⊔ R₂) ⊓ Subgroup.normalizer ((S ⊓ (R₁ ⊔ R₂) : Subgroup A) : Set A)) →
    IsCyclic ↥D → Odd (Nat.card ↥D) →
    D ≤ Subgroup.normalizer ((Q₁ ⊔ Q₂ : Subgroup A) : Set A) →
    B ≤ Subgroup.normalizer (D : Set A) → (D : Set A) * (S : Set A) = (S : Set A) * (D : Set A) →
    D ≤ B ⊔ Subgroup.centralizer ((Q₁ ⊔ Q₂ : Subgroup A) : Set A)

section Bar

variable {G : Type} [Group G] [Finite G]

theorem modO2Image_inf_normalizer {X K P : Subgroup G} (hKX : K ≤ X) (hPK : P ≤ K)
    (hOP : K ⊓ pCoreOf 2 X ≤ P) :
    modO2Image X (K ⊓ Subgroup.normalizer (P : Set G)) =
      modO2Image X K ⊓ Subgroup.normalizer ((modO2Image X P : Subgroup (O2Q X)) : Set (O2Q X)) := by
  apply le_antisymm
  · refine le_inf (Subgroup.map_mono fun x hx => hx.1) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact o2Map_mem_normalizer hx.2
  · rintro _ ⟨⟨k, hk, rfl⟩, hkn⟩
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    refine ⟨k, Subgroup.mem_subgroupOf.mpr ⟨hkK, ?_⟩, rfl⟩
    refine mem_normalizer_of_conj_mem' fun p hp => ?_
    have hpX : p ∈ X := hKX (hPK hp)
    obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_normalizer_iff.mp hkn
      (QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨p, hpX⟩)).mp ⟨⟨p, hpX⟩, hp, rfl⟩
    have h2 : y⁻¹ * (k * ⟨p, hpX⟩ * k⁻¹) ∈ CFSG.pCore 2 ↥X := by
      have h' : QuotientGroup.mk' (CFSG.pCore 2 ↥X) y =
          QuotientGroup.mk' (CFSG.pCore 2 ↥X) (k * ⟨p, hpX⟩ * k⁻¹) := by
        rw [hyx, map_mul, map_mul, map_inv]
      rwa [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h'
    have h2' : y⁻¹ * (k * ⟨p, hpX⟩ * k⁻¹) ∈ CFSG.Open.pCore 2 ↥X := by
      exact h2
    have hyP : (y : G) ∈ P := Subgroup.mem_subgroupOf.mp hy
    have hzK : ((y⁻¹ * (k * ⟨p, hpX⟩ * k⁻¹) : ↥X) : G) ∈ K := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact K.mul_mem (K.inv_mem (hPK hyP)) (K.mul_mem (K.mul_mem hkK (hPK hp)) (K.inv_mem hkK))
    have hzP := hOP ⟨hzK, ⟨_, h2', rfl⟩⟩
    have e : (k : G) * p * (k : G)⁻¹ = (y : G) * ((y⁻¹ * (k * ⟨p, hpX⟩ * k⁻¹) : ↥X) : G) := by
      simp
    rw [e]
    exact P.mul_mem hyP hzP

theorem isHallTwoPrimeOf_modO2Image {X B Y : Subgroup G} (hYX : Y ≤ X)
    (hB : Lin2.IsHallTwoPrimeOf B Y) :
    Lin2.IsHallTwoPrimeOf (modO2Image X B) (modO2Image X Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBY, hodd, k, hk⟩ := hB
  have hBX : B ≤ X := hBY.trans hYX
  have hBcard : Nat.card (modO2Image X B) = Nat.card B := by
    have h0 := Subgroup.card_ker_mul_card_of_surjective (barMap_surjective hBX)
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (isPGroup_ker_barMap hBX)
    have hj0 : j = 0 := by
      by_contra hj0
      have h2 : 2 ∣ Nat.card B := by
        rw [← h0, hj]
        exact Dvd.dvd.mul_right (dvd_pow_self 2 hj0) _
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    rw [hj, hj0, pow_zero, one_mul] at h0
    exact h0
  have hBbY : modO2Image X B ≤ modO2Image X Y := Subgroup.map_mono fun x hx => hBY hx
  refine ⟨hBbY, hBcard ▸ hodd, ?_⟩
  have h1 : (modO2Image X B).relIndex (modO2Image X Y) * Nat.card (modO2Image X B) =
      Nat.card (modO2Image X Y) := by
    have := Subgroup.relIndex_mul_card (modO2Image X B) (modO2Image X Y)
    rwa [inf_eq_left.mpr hBbY] at this
  have h2 : Nat.card (modO2Image X Y) ∣ Nat.card Y :=
    Subgroup.card_dvd_of_surjective (barMap_surjective hYX)
  have h3 : Nat.card Y = 2 ^ k * Nat.card B := by
    have := Subgroup.relIndex_mul_card B Y
    rw [inf_eq_left.mpr hBY, hk] at this
    exact this.symm
  rw [← h1, h3, hBcard] at h2
  have h4 : (modO2Image X B).relIndex (modO2Image X Y) ∣ 2 ^ k :=
    Nat.dvd_of_mul_dvd_mul_right Nat.card_pos h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
  exact ⟨j, hj⟩

theorem mem_normalizer_of_modO2Image {X K : Subgroup G} (hKX : K ≤ X) (hK : ⁅K, K⁆ = K)
    (hOK : pCoreOf 2 X ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ X)
    (hxK : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hx⟩ ∈
      Subgroup.normalizer ((modO2Image X K : Subgroup (O2Q X)) : Set (O2Q X))) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmK : K.map (MulAut.conj x).toMonoidHom ≤ K := by
    refine le_of_perfect_of_le_sup (by rw [← Subgroup.map_commutator, hK]) ?_
      (pCoreOf_isPGroup 2 X) hOK
    rintro _ ⟨y, hy, rfl⟩
    have hyX : y ∈ X := hKX hy
    obtain ⟨z, hz, hzy⟩ := (Subgroup.mem_normalizer_iff.mp hxK
      (QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨y, hyX⟩)).mp ⟨⟨y, hyX⟩, hy, rfl⟩
    have h2 : z⁻¹ * (⟨x, hx⟩ * ⟨y, hyX⟩ * ⟨x, hx⟩⁻¹) ∈ CFSG.pCore 2 ↥X := by
      have h' : QuotientGroup.mk' (CFSG.pCore 2 ↥X) z =
          QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨x, hx⟩ * ⟨y, hyX⟩ * ⟨x, hx⟩⁻¹) := by
        rw [hzy, map_mul, map_mul, map_inv]
      rwa [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h'
    have h2' : z⁻¹ * (⟨x, hx⟩ * ⟨y, hyX⟩ * ⟨x, hx⟩⁻¹) ∈ CFSG.Open.pCore 2 ↥X := by
      exact h2
    have h3 : (MulAut.conj x).toMonoidHom y = (z : G) *
        ((z⁻¹ * (⟨x, hx⟩ * ⟨y, hyX⟩ * ⟨x, hx⟩⁻¹) : ↥X) : G) := by
      simp [MulAut.conj_apply]
    rw [h3]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hz))
      (Subgroup.mem_sup_right ⟨_, h2', rfl⟩)
  exact mem_normalizer_of_conj_mem' fun y hy => hmK ⟨y, hy, rfl⟩

omit [Finite G] in
theorem modO2Image_mul_comm {X A C : Subgroup G} (hAX : A ≤ X) (hCX : C ≤ X)
    (h₁ : ∀ a ∈ A, ∀ c ∈ C, ∃ a' ∈ A, ∃ c' ∈ C, c * a = a' * c')
    (h₂ : ∀ a ∈ A, ∀ c ∈ C, ∃ c' ∈ C, ∃ a' ∈ A, a * c = c' * a') :
    (modO2Image X A : Set (O2Q X)) * (modO2Image X C : Set (O2Q X)) =
      (modO2Image X C : Set (O2Q X)) * (modO2Image X A : Set (O2Q X)) := by
  ext x
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨c, hc, rfl⟩, rfl⟩
    obtain ⟨c', hc', a', ha', he⟩ :=
      h₂ a (Subgroup.mem_subgroupOf.mp ha) c (Subgroup.mem_subgroupOf.mp hc)
    refine ⟨_, ⟨⟨c', hCX hc'⟩, Subgroup.mem_subgroupOf.mpr hc', rfl⟩, _,
      ⟨⟨a', hAX ha'⟩, Subgroup.mem_subgroupOf.mpr ha', rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext he.symm)
  · rintro ⟨_, ⟨c, hc, rfl⟩, _, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨a', ha', c', hc', he⟩ :=
      h₁ a (Subgroup.mem_subgroupOf.mp ha) c (Subgroup.mem_subgroupOf.mp hc)
    refine ⟨_, ⟨⟨a', hAX ha'⟩, Subgroup.mem_subgroupOf.mpr ha', rfl⟩, _,
      ⟨⟨c', hCX hc'⟩, Subgroup.mem_subgroupOf.mpr hc', rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext he.symm)

end Bar

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {n : ℕ}

theorem exists_mul_eq_of_hall (h : Hyp5_0_1 G T M L n) {D X : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) (hTX : T ≤ X) {d s : G} (hd : d ∈ D ⊓ X)
    (hs : s ∈ T) : ∃ d' ∈ D ⊓ X, ∃ s' ∈ T, s * d = d' * s' := by
  have hDB : D ≤ borelL T L := hD.1
  have hDN : D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := hDB.trans inf_le_right
  have hsd : s * d * s⁻¹ ∈ borelL T L :=
    (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer_borel hs) d).mp (hDB hd.1)
  have hmem : (s * d * s⁻¹)⁻¹ ∈ (T ⊓ L) ⊔ D := by
    rw [sup_comm, h.borelL_eq_sup hD]
    exact (borelL T L).inv_mem hsd
  obtain ⟨a, ha, d₀, hd₀, he⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hDN).mp hmem
  have h1 : s * d * s⁻¹ = d₀⁻¹ * a⁻¹ := by
    rw [← mul_inv_rev, ← he, inv_inv]
  have hd₀X : d₀⁻¹ ∈ X := by
    have e : d₀⁻¹ = s * d * s⁻¹ * a := by
      rw [h1]
      group
    rw [e]
    exact X.mul_mem (X.mul_mem (X.mul_mem (hTX hs) hd.2) (X.inv_mem (hTX hs))) (hTX ha.1)
  refine ⟨d₀⁻¹, ⟨D.inv_mem hd₀, hd₀X⟩, a⁻¹ * s, T.mul_mem (T.inv_mem ha.1) hs, ?_⟩
  calc s * d = s * d * s⁻¹ * s := by group
    _ = d₀⁻¹ * (a⁻¹ * s) := by
      rw [h1]
      group

theorem exists_mul_eq_of_hall' (h : Hyp5_0_1 G T M L n) {D X : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) (hTX : T ≤ X) {d s : G} (hd : d ∈ D ⊓ X)
    (hs : s ∈ T) : ∃ s' ∈ T, ∃ d' ∈ D ⊓ X, d * s = s' * d' := by
  obtain ⟨d', hd', s', hs', he⟩ := h.exists_mul_eq_of_hall hD hTX
    (⟨D.inv_mem hd.1, X.inv_mem hd.2⟩ : d⁻¹ ∈ D ⊓ X) (T.inv_mem hs)
  refine ⟨s'⁻¹, T.inv_mem hs', d'⁻¹, ⟨D.inv_mem hd'.1, X.inv_mem hd'.2⟩, ?_⟩
  calc d * s = (s⁻¹ * d⁻¹)⁻¹ := by group
    _ = s'⁻¹ * d'⁻¹ := by
      rw [he]
      group

end Hyp5_0_1

namespace Main513

variable {G : Type} [Group G] [Finite G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem inf_le_normalizer_of_c2 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1281 : Lemma128One) (h510 : Stmt5_1_10)
    (hF : FactC2Hall) (m : Main513 G T M L V H B D K₁ X Kh₁ n) (hlt : K₁ < oTwoUpper H)
    (hL24 : LieModel (O2Q K₁) .PSL 2 2 2)
    (htype : IsSporadic .J1 (O2Q Kh₁) ∨
      ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 (O2Q Kh₁)) :
    D ⊓ X ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hHO : pCoreOf 2 H ≠ ⊥ := m.hyp.hStar.1.2
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hHX : H ≤ X := m.inH.1
  have hXO : pCoreOf 2 X ≠ ⊥ := m.inH.2
  have hTX : T ≤ X := hTH.1.trans hHX
  have hTXs : IsSylowTwoOf T X := h.isSylowTwoOf hTX
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKX : oTwoUpper H ≤ X := hKH.trans hHX
  have hK₁c : K₁ ∈ cComp H := m.comp
  have hK₁H : K₁ ≤ H := le_of_mem_cComp hK₁c
  have hK₁X : K₁ ≤ X := hK₁H.trans hHX
  have hKhc : Kh₁ ∈ cComp X := m.hat.1
  have hKhX : Kh₁ ≤ X := le_of_mem_cComp hKhc
  have hK₁Kh : K₁ ≤ Kh₁ := m.hat.2.1
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [m.closure]
    exact le_normalizer_conjClosure K₁ T
  have hKperf : ⁅oTwoUpper H, oTwoUpper H⁆ = oTwoUpper H := by
    rw [m.closure]
    exact A3.conjClosure_perfect m.comp.2.1
  have hOT : pCoreOf 2 X ≤ T := F7.isSylowTwoOf_pCoreOf_le hTXs
  obtain ⟨K₂, tc⟩ := exists_twoComp h38 hloc hHO hTH hK₁c m.closure hlt
  obtain ⟨t, ht, hK₂⟩ := tc.conj
  have htX : t ∈ X := hTX ht
  have hK₂X : K₂ ≤ X := (le_of_mem_cComp tc.cK₂).trans hHX
  have hhat : ∀ g ∈ X, g ∈ Subgroup.normalizer (K₁ : Set G) →
      g ∈ Subgroup.normalizer (Kh₁ : Set G) := by
    intro g hg hgN
    have hKg : Kh₁.map (MulAut.conj g).toMonoidHom ∈ cComp X := map_conj_mem_cComp hKhc hg
    have hK₁g : K₁ ≤ Kh₁.map (MulAut.conj g).toMonoidHom :=
      calc K₁ = K₁.map (MulAut.conj g).toMonoidHom := (A38.map_conj_eq_iff.mpr hgN).symm
        _ ≤ Kh₁.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hK₁Kh
    exact A38.map_conj_eq_iff.mp (m.hat.2.2 _ hKg hK₁g)
  have hconjKh : ∀ g ∈ T, Kh₁.map (MulAut.conj g).toMonoidHom = Kh₁ ∨
      Kh₁.map (MulAut.conj g).toMonoidHom = Kh₁.map (MulAut.conj t).toMonoidHom := by
    intro g hg
    have hgX : g ∈ X := hTX hg
    have h1 : K₁.map (MulAut.conj g).toMonoidHom ∈ cComp H :=
      map_conj_mem_cComp hK₁c (hTH.1 hg)
    have h2 : K₁.map (MulAut.conj g).toMonoidHom ≤ oTwoUpper H := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hTK hg) y).mp (hlt.le hy)
    rcases tc.cK _ (cComp_mem_of_le h1 h2 hKH) with h3 | h3
    · exact Or.inl (A38.map_conj_eq_iff.mpr (hhat g hgX (A38.map_conj_eq_iff.mp h3)))
    · right
      have h4 : t⁻¹ * g ∈ Subgroup.normalizer (K₁ : Set G) := by
        refine mem_normalizer_of_conj_mem' fun y hy => ?_
        have hy' : g * y * g⁻¹ ∈ K₁.map (MulAut.conj t).toMonoidHom := by
          rw [← hK₂, ← h3]
          exact ⟨y, hy, rfl⟩
        obtain ⟨z, hz, hzy⟩ := hy'
        have hzy' : t * z * t⁻¹ = g * y * g⁻¹ := hzy
        have e : t⁻¹ * g * y * (t⁻¹ * g)⁻¹ = z :=
          calc t⁻¹ * g * y * (t⁻¹ * g)⁻¹ = t⁻¹ * (g * y * g⁻¹) * t := by group
            _ = t⁻¹ * (t * z * t⁻¹) * t := by rw [hzy']
            _ = z := by group
        rw [e]
        exact hz
      have h5 := hhat _ (X.mul_mem (X.inv_mem htX) hgX) h4
      have e : Kh₁.map (MulAut.conj g).toMonoidHom =
          (Kh₁.map (MulAut.conj (t⁻¹ * g)).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        group
      rw [e, A38.map_conj_eq_iff.mpr h5]
  have hne : Kh₁.map (MulAut.conj t).toMonoidHom ≠ Kh₁ := by
    intro he
    have htN : t ∈ Subgroup.normalizer (Kh₁ : Set G) := A38.map_conj_eq_iff.mp he
    have hloc₁ : quasithinIsLocal T K₁ := isLocal_of_mem_cComp_of_sylow hTH hHO hK₁c
    have hlocH : quasithinIsLocal T Kh₁ := isLocal_of_mem_cComp_of_sylow hTXs hXO hKhc
    have htK₁ := h1281 G h.qtke h.simple h.nonabelian T K₁ Kh₁ hloc₁ hlocH hK₁Kh ⟨ht, htN⟩
    apply tc.ne
    rw [hK₂]
    exact A38.map_conj_eq_iff.mpr htK₁
  have hKht : Kh₁.map (MulAut.conj t).toMonoidHom ∈ cComp X := map_conj_mem_cComp hKhc htX
  have hKheq : conjClosure Kh₁ T = Kh₁ ⊔ Kh₁.map (MulAut.conj t).toMonoidHom := by
    refine le_antisymm (conjClosure_le fun g hg y hy => ?_) (sup_le (le_conjClosure Kh₁ T) ?_)
    · have hm : g * y * g⁻¹ ∈ Kh₁.map (MulAut.conj g).toMonoidHom :=
        ⟨y, hy, by simp [MulAut.conj_apply]⟩
      rcases hconjKh g hg with h1 | h1
      · rw [h1] at hm
        exact Subgroup.mem_sup_left hm
      · rw [h1] at hm
        exact Subgroup.mem_sup_right hm
    · rintro _ ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using mem_conjClosure ht hy
  have hXN : X ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 hXO hTXs hKhc
  set s : O2Q X := QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨t, htX⟩ with hs
  set Q₁ := modO2Image X Kh₁ with hQ₁
  set Q₂ := modO2Image X (Kh₁.map (MulAut.conj t).toMonoidHom) with hQ₂
  have hQ₂s : Q₂ = Q₁.map (MulAut.conj s).toMonoidHom := modO2Image_conj (L := Kh₁) ⟨t, htX⟩
  set R₁ := modO2Image X K₁ with hR₁
  set R₂ := modO2Image X K₂ with hR₂
  have hR₂s : R₂ = R₁.map (MulAut.conj s).toMonoidHom := by
    rw [hR₂, hK₂]
    exact modO2Image_conj ⟨t, htX⟩
  set S := modO2Image X T with hS
  have hsS : s ∈ S := ⟨⟨t, htX⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hSsyl : IsSylowTwoOf S ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hTXs) _
      (QuotientGroup.mk'_surjective _)
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hloc hXO
  have hQ₁c : Q₁ ∈ cComp (⊤ : Subgroup (O2Q X)) := modO2Image_mem_cComp hKhc
  have hQ₂ne : Q₂ ≠ Q₁ := fun he => hne (modO2Image_injOn X hKht hKhc he)
  have hQ₂mem : Q₂ ∈ conjSubgroupsBy S Q₁ := ⟨s, hsS, hQ₂s⟩
  obtain ⟨hcomm, hinf⟩ : ⁅Q₁, Q₂⁆ = ⊥ ∧ Q₁ ⊓ Q₂ = ⊥ := by
    rcases ((h38 _ hQ) _ hQ₁c).2 _ hSsyl with ⟨-, hcs, -⟩ |
        ⟨tb, -, -, hcs, -, hcomm, hinf, -, -⟩
    · rw [hcs] at hQ₂mem
      exact absurd hQ₂mem hQ₂ne
    · rw [hcs] at hQ₂mem
      rcases hQ₂mem with h1 | h1
      · exact absurd h1 hQ₂ne
      · rw [show Q₂ = Q₁.map (MulAut.conj tb).toMonoidHom from h1]
        exact ⟨hcomm, hinf⟩
  have hQeq : modO2Image X (conjClosure Kh₁ T) = Q₁ ⊔ Q₂ := by
    rw [hKheq]
    exact modO2Image_sup hKhX (le_of_mem_cComp hKht)
  have hQN : ∀ y : O2Q X,
      y ∈ Subgroup.normalizer ((Q₁ ⊔ Q₂ : Subgroup (O2Q X)) : Set (O2Q X)) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) y
    rw [← hQeq]
    exact o2Map_mem_normalizer (hXN x.2)
  have hSQ : IsSylowTwoOf (S ⊓ (Q₁ ⊔ Q₂)) (Q₁ ⊔ Q₂) :=
    A4.isSylowTwoOf_inf_normal hSsyl le_top fun y _ => hQN y
  have hReq : R₁ ⊔ R₂ = modO2Image X (oTwoUpper H) := by
    rw [tc.sup]
    exact (modO2Image_sup hK₁X hK₂X).symm
  have hR₁Q₁ : R₁ ≤ Q₁ := Subgroup.map_mono fun x hx => hK₁Kh hx
  have hR₁perf : ⁅R₁, R₁⁆ = R₁ := by
    have : Group.IsPerfect ↥K₁ := Subgroup.isPerfect_iff.mpr m.comp.2.1
    have : Group.IsPerfect ↥R₁ := Group.IsPerfect.ofSurjective (barMap_surjective hK₁X)
    exact Subgroup.isPerfect_iff.mp this
  have hR₁L : LieModel (ModO2 R₁) .PSL 2 2 2 := by
    obtain ⟨e⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hK₁X
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hL24
  have hTKb : S ≤ Subgroup.normalizer
      ((modO2Image X (oTwoUpper H) : Subgroup (O2Q X)) : Set (O2Q X)) :=
    Vol2.Ch11.SecS.modO2Image_le_normalizer hTK
  have hSR : IsSylowTwoOf (S ⊓ (R₁ ⊔ R₂)) (R₁ ⊔ R₂) := by
    rw [hReq]
    exact A4.isSylowTwoOf_inf_normal (QuasithinUnique.isSylowTwoOf_of_le hSsyl le_sup_right)
      le_sup_left (sup_le Subgroup.le_normalizer hTKb)
  obtain ⟨-, -, hBorel, hHall, -⟩ := h510 G T M L H B D n m.hyp m.nota
  have hBK : B ≤ oTwoUpper H := hHall.1.trans inf_le_right
  rw [m.hyp.borel_eq hBorel] at hHall
  have hBb : Lin2.IsHallTwoPrimeOf (modO2Image X B)
      ((R₁ ⊔ R₂) ⊓ Subgroup.normalizer ((S ⊓ (R₁ ⊔ R₂) : Subgroup (O2Q X)) : Set (O2Q X))) := by
    have h1 := isHallTwoPrimeOf_modO2Image (X := X) (inf_le_left.trans hKX) hHall
    rwa [modO2Image_inf_normalizer hKX inf_le_right (fun x hx => ⟨hOT hx.2, hx.1⟩),
      ← modO2Image_inf_of_pCoreOf_le hOT, ← hReq] at h1
  have hD := m.nota.2.1
  have hDcyc : IsCyclic ↥D := (h.isCyclic_card_of_isHall l2TorusFact hD).1
  have hDXcyc : IsCyclic ↥(D ⊓ X) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe (inf_le_left : D ⊓ X ≤ D)).toMonoidHom
      (MulEquiv.surjective _)
  have hDbcyc : IsCyclic ↥(modO2Image X (D ⊓ X)) :=
    isCyclic_of_surjective (barMap inf_le_right) (barMap_surjective inf_le_right)
  have hDbodd : Odd (Nat.card ↥(modO2Image X (D ⊓ X))) :=
    Odd.of_dvd_nat hD.2.1 ((Subgroup.card_dvd_of_surjective (barMap_surjective inf_le_right)).trans
      (Subgroup.card_dvd_of_le inf_le_left))
  have hBX : B ≤ X := hBK.trans hKX
  have hBDX : B ≤ Subgroup.normalizer ((D ⊓ X : Subgroup G) : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨m.nota.2.2 hb, Subgroup.le_normalizer (hBX hb)⟩
  have hBbD : modO2Image X B ≤
      Subgroup.normalizer ((modO2Image X (D ⊓ X) : Subgroup (O2Q X)) : Set (O2Q X)) :=
    Vol2.Ch11.SecS.modO2Image_le_normalizer hBDX
  have hperm : (modO2Image X (D ⊓ X) : Set (O2Q X)) * (S : Set (O2Q X)) =
      (S : Set (O2Q X)) * (modO2Image X (D ⊓ X) : Set (O2Q X)) :=
    modO2Image_mul_comm inf_le_right hTX
      (fun d hd c hc => h.exists_mul_eq_of_hall hD hTX hd hc)
      (fun d hd c hc => h.exists_mul_eq_of_hall' hD hTX hd hc)
  have hQ₁type : IsSporadic .J1 ↥Q₁ ∨
      ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 ↥Q₁ := by
    obtain ⟨e⟩ := modO2_mulEquiv hKhc
    rcases htype with hJ | ⟨p, hp, h5, h8, hP⟩
    · exact Or.inl (IsSporadic.of_mulEquiv e hJ)
    · exact Or.inr ⟨p, hp, h5, h8, IsPSL.of_mulEquiv e hP⟩
  have key := hF (O2Q X) Q₁ Q₂ R₁ R₂ S (modO2Image X B) (modO2Image X (D ⊓ X)) s hQ₁type hsS
    hQ₂s hR₂s hcomm hinf hSsyl.2.1 (fun y _ => hQN y) hSQ hR₁Q₁ hR₁perf hR₁L hSR hBb hDbcyc
    hDbodd (fun y _ => hQN y) hBbD hperm
  have hKbQ : modO2Image X (oTwoUpper H) ≤ Q₁ ⊔ Q₂ := by
    rw [← hReq]
    refine sup_le_sup hR₁Q₁ ?_
    rw [hR₂s, hQ₂s]
    exact Subgroup.map_mono hR₁Q₁
  have hKbN : modO2Image X B ⊔ Subgroup.centralizer ((Q₁ ⊔ Q₂ : Subgroup (O2Q X)) : Set (O2Q X)) ≤
      Subgroup.normalizer ((modO2Image X (oTwoUpper H) : Subgroup (O2Q X)) : Set (O2Q X)) :=
    sup_le ((show modO2Image X B ≤ modO2Image X (oTwoUpper H) from
        Subgroup.map_mono fun x hx => hBK hx).trans Subgroup.le_normalizer)
      ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hKbQ)).trans
        (Subgroup.centralizer_le_normalizer _))
  intro d hd
  have hdb : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨d, hd.2⟩ ∈ modO2Image X (D ⊓ X) :=
    ⟨⟨d, hd.2⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
  exact mem_normalizer_of_modO2Image hKX hKperf (hOT.trans hTK) hd.2 (hKbN (key hdb))

end Main513

theorem stmt5_1_13_c2_of (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1281 : Lemma128One) (h510 : Stmt5_1_10) (hF : FactC2Hall) : Stmt5_1_13_c2 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hlt hL24 htype
  exact m.not_le (m.inf_le_normalizer_of_c2 h37 h38 h1281 h510 hF hlt hL24 htype)

end CFSG.Quasithin.H13
