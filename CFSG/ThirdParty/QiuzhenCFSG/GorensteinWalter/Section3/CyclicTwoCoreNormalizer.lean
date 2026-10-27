module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreKleinFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.KleinFourTransitive

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- The centralizer `C_U(V)` of a subgroup `V` inside the odd core `U`. -/
public noncomputable def Ucentralizer {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G) (V : Subgroup G) : Subgroup G :=
  bg.U ⊓ Subgroup.centralizer (V : Set G)

/-- If `H = U·S` with `S` a `2`-group and `U ◁ H`, then every element of
`H` of odd order lies in `U`. -/
public theorem element_le_U_of_odd_order
    {G : Type u} [Group G] [Finite G]
    (U S H : Subgroup G) (hUS : U ⊔ S = H)
    (hUnorm : IsNormalIn U H) (hS2 : IsPGroup 2 S)
    {x : G} (hxH : x ∈ H) (hodd : Nat.Coprime 2 (orderOf x)) :
    x ∈ U := by
  classical
  have hUleH : U ≤ H := by
    intro u hu
    exact (le_of_eq hUS) (Subgroup.mem_sup_left hu)
  have hSleH : S ≤ H := by
    intro s hs
    exact (le_of_eq hUS) (Subgroup.mem_sup_right hs)
  let U0 : Subgroup H := U.subgroupOf H
  let S0 : Subgroup H := S.subgroupOf H
  have hU0norm : U0.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUleH]
    exact fun h k hh hk => hUnorm.2 k hk h hh
  have hU0S0 : U0 ⊔ S0 = ⊤ := by
    apply le_antisymm
    · exact le_top
    · intro x0 hx0
      have hsub : U0 ⊔ S0 = (U ⊔ S).subgroupOf H := by
        symm
        exact Subgroup.subgroupOf_sup (A := U) (A' := S) (B := H)
          hUleH hSleH
      rw [hsub, hUS, Subgroup.subgroupOf_self]
      trivial
  let : U0.Normal := hU0norm
  let q : H →* H ⧸ U0 := QuotientGroup.mk' U0
  let xH : H := ⟨x, hxH⟩
  have hxUS : xH ∈ U0 ⊔ S0 := by
    rw [hU0S0]
    trivial
  rcases (Subgroup.mem_sup_of_normal_left (s := U0) (t := S0)).mp hxUS with
    ⟨u, hu, s, hs, hxs⟩
  have hqS : q xH ∈ S0.map q := by
    have hxq : q xH = q s := by
      calc
        q xH = q (u * s) := by rw [← hxs]
        _ = q u * q s := by rw [map_mul]
        _ = q s := by
          have hqu : q u = 1 := by
            have hker : MonoidHom.ker q = U0 := QuotientGroup.ker_mk' U0
            exact (MonoidHom.mem_ker).mp (by simpa [hker] using hu)
          rw [hqu]
          simp
    exact Subgroup.mem_map.mpr ⟨s, hs, hxq.symm⟩
  have hS2 : IsPGroup 2 S0 := by
    exact hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSleH).symm
  have hqS2 : IsPGroup 2 (S0.map q) := hS2.map q
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hqS2) ⟨q xH, hqS⟩
  have hqorder : orderOf (q xH) = 2 ^ k := by
    simpa using hk
  have hk0 : k = 0 := by
    by_contra hk0
    have h2dvd : 2 ∣ orderOf (q xH) := by
      rw [hqorder]
      exact ⟨2 ^ (k - 1), by
        rw [show k = (k - 1) + 1 by omega, pow_succ']
        rfl⟩
    have hdiv : orderOf (q xH) ∣ orderOf xH := orderOf_map_dvd q xH
    have horder : orderOf xH = orderOf x := by
      simpa [xH] using (Subgroup.orderOf_mk (⟨x, hxH⟩ : H))
    have h2dvd' : 2 ∣ orderOf x := h2dvd.trans (hdiv.trans (by rw [horder]))
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hodd h2dvd'
  have hq1 : q xH = 1 := by
    apply orderOf_eq_one_iff.mp
    rw [hqorder, hk0]
    simp
  have hxU0 : xH ∈ U0 := by
    have hker : MonoidHom.ker q = U0 := QuotientGroup.ker_mk' U0
    simpa [hker] using (MonoidHom.mem_ker).mpr hq1
  exact (Subgroup.mem_subgroupOf.mp hxU0)

/-- `U = O(H)` is normal in `H`. -/
public theorem bg_U_normal_in_H
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G) : IsNormalIn bg.U bg.H := by
  refine ⟨Subgroup.map_subtype_le (H := bg.H) (pPrimeCore 2 bg.H), ?_⟩
  intro h hh x hx
  rcases (Subgroup.mem_map).1 hx with ⟨p2, hp2, rfl⟩
  have hconj : (⟨h, hh⟩ : bg.H) * p2 * (⟨h, hh⟩ : bg.H)⁻¹ ∈
      pPrimeCore 2 bg.H :=
    (pPrimeCore_normal (p := 2) (G := bg.H)).conj_mem p2 hp2 ⟨h, hh⟩
  exact Subgroup.mem_map.mpr
    ⟨(⟨h, hh⟩ : bg.H) * p2 * (⟨h, hh⟩ : bg.H)⁻¹, hconj, by simp⟩

/-- In `H = U·S`, every odd-order element of `H` lies in `U`. -/
public theorem element_le_U_of_le_H_of_odd_order
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G)
    {x : G} (hxH : x ∈ bg.H) (hodd : Nat.Coprime 2 (orderOf x)) :
    x ∈ bg.U := by
  exact element_le_U_of_odd_order bg.U (bg.S : Subgroup G) bg.H
    (by simpa [BenderGlauberman.Hyp11.U] using bg.H_eq_US)
    (bg_U_normal_in_H bg) bg.S.isPGroup' hxH hodd

/-- If `H = U·S` with `S` a `2`-group and `p` an odd prime, then every
`p`-subgroup of `H` lies in `U`. -/
public theorem pSubgroup_le_U_of_le_H
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G)
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    {X : Subgroup G} (hXleH : X ≤ bg.H) (hXp : IsPGroup p X) :
    X ≤ bg.U := by
  intro x hx
  apply element_le_U_of_le_H_of_odd_order bg (hXleH hx)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hXp) ⟨x, hx⟩
  have hxorder : orderOf x = p ^ n := by
    simpa using hn
  rw [hxorder]
  exact Nat.Prime.coprime_pow_of_not_dvd Fact.out (by
    intro hp2
    exact hpodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hp2))

/-- For `V = ⟨t, s⟩`, the `s`-centralizer in `U` equals the `V`-centralizer
in `U` whenever `U` centralizes `t`. -/
private theorem centralizerIn_eq_centralizer_subgroup_of_closure
    {G : Type u} [Group G]
    (U : Subgroup G) {V : Subgroup G} {t s : G}
    (hV : V = Subgroup.closure ({t, s} : Set G))
    (hUcent : U ≤ Subgroup.centralizer ({t} : Set G)) :
    centralizerIn U s = U ⊓ Subgroup.centralizer (V : Set G) := by
  have hCV : Subgroup.centralizer (V : Set G) =
      Subgroup.centralizer ({t, s} : Set G) := by
    rw [hV, Subgroup.centralizer_closure]
  ext x
  constructor
  · intro hx
    have hxU : x ∈ U := (Subgroup.mem_inf.mp hx).1
    have hxCs : x ∈ Subgroup.centralizer ({s} : Set G) :=
      (Subgroup.mem_inf.mp hx).2
    refine ⟨hxU, ?_⟩
    rw [hV, Subgroup.centralizer_closure]
    change x ∈ Subgroup.centralizer ({t, s} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with (rfl | rfl)
    · exact (Subgroup.mem_centralizer_iff.mp (hUcent hxU)) y (by simp)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hxCs).symm
  · intro hx
    have hxU : x ∈ U := (Subgroup.mem_inf.mp hx).1
    have hxC : x ∈ Subgroup.centralizer (V : Set G) := (Subgroup.mem_inf.mp hx).2
    have hxCs : x ∈ Subgroup.centralizer ({s} : Set G) := by
      have hxC' : x ∈ Subgroup.centralizer ({t, s} : Set G) := by
        rw [hV, Subgroup.centralizer_closure] at hxC
        exact hxC
      exact (Subgroup.centralizer_le (by simp : ({s} : Set G) ⊆ {t, s}))
        hxC'
    exact Subgroup.mem_inf.mpr ⟨hxU, hxCs⟩

/-- Frattini transfer: if `P` is a Sylow `p`-subgroup of the
`U`-centralizer of `V` (with `U` the odd core of `H = C_G(t)`), then the
conjugation action of `N_G(V)` on `V` is realised inside `N_G(P)`. -/
public theorem frattini_transfer_conj
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G)
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    {V P : Subgroup G}
    (hVmem : bg.t ∈ V)
    (hPleK : P ≤ Ucentralizer bg V)
    (hPcard : Nat.card P =
      p ^ (Nat.card (Ucentralizer bg V)).factorization p)
    {x g : G} (hx : x ∈ V)
    (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    ∃ m : G, m ∈ Subgroup.normalizer (P : Set G) ∧
      m * x * m⁻¹ = g * x * g⁻¹ := by
  classical
  let K : Subgroup G := bg.U ⊓ Subgroup.centralizer (V : Set G)
  let P' : Subgroup G := P.map (MulAut.conj g).toMonoidHom
  let PK : Sylow p K := Sylow.ofCard (P.subgroupOf K) (by
    calc
      Nat.card (P.subgroupOf K) = Nat.card P := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleK).toEquiv
      _ = p ^ (Nat.card K).factorization p := hPcard)
  have hP'leC : P' ≤ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    intro v hv p' hp'
    rcases (Subgroup.mem_map).1 hp' with ⟨y, hy, rfl⟩
    have hyC : y ∈ Subgroup.centralizer (V : Set G) :=
      (Subgroup.mem_inf.mp (hPleK hy)).2
    have hgv : g⁻¹ * v * g ∈ V :=
      (Subgroup.mem_normalizer_iff''.mp hg v).1 hv
    have hyv : y * (g⁻¹ * v * g) = (g⁻¹ * v * g) * y :=
      ((Subgroup.mem_centralizer_iff.mp hyC) (g⁻¹ * v * g) hgv).symm
    calc
      (g * y * g⁻¹) * v = g * (y * (g⁻¹ * v * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * v * g) * y) * g⁻¹ := by rw [hyv]
      _ = v * (g * y * g⁻¹) := by group
  have hP'leH : P' ≤ bg.H := by
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (V : Set G) := hP'leC hz
    have hzC' : z ∈ Subgroup.centralizer ({bg.t} : Set G) :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hVmem)) hzC
    rwa [bg.H_eq_centralizer]
  have hPp : IsPGroup p P := IsPGroup.of_card (by rw [hPcard])
  have hP'p : IsPGroup p P' := hPp.map (MulAut.conj g).toMonoidHom
  have hP'leU : P' ≤ bg.U := pSubgroup_le_U_of_le_H bg p hpodd hP'leH hP'p
  have hP'leK : P' ≤ K := by
    intro z hz
    exact Subgroup.mem_inf.mpr ⟨hP'leU hz, hP'leC hz⟩
  have hP'card : Nat.card P' = p ^ (Nat.card K).factorization p := by
    calc
      Nat.card P' = Nat.card P := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      _ = p ^ (Nat.card K).factorization p := hPcard
  let P'K : Sylow p K := Sylow.ofCard (P'.subgroupOf K) (by
    calc
      Nat.card (P'.subgroupOf K) = Nat.card P' := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'leK).toEquiv
      _ = p ^ (Nat.card K).factorization p := hP'card)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K P'K PK
  have hc' : (P'.subgroupOf K).map (MulAut.conj c).toMonoidHom =
      P.subgroupOf K := by
    have h := congrArg (fun Q : Sylow p K => (Q : Subgroup K)) hc
    rw [Sylow.coe_subgroup_smul] at h
    have hsmul : MulAut.conj c • (P'K : Subgroup K) =
        (P'K : Subgroup K).map (MulAut.conj c).toMonoidHom := by
      ext z
      rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
      constructor
      · rintro ⟨h, hh, hz⟩
        exact ⟨h, hh, by simpa [MulAut.smul_def] using hz⟩
      · rintro ⟨h, hh, hz⟩
        exact ⟨h, hh, by simpa [MulAut.smul_def] using hz⟩
    rw [hsmul] at h
    simpa [P'K, PK, Sylow.coe_ofCard] using h
  have hcomm : K.subtype.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj (c : G)).toMonoidHom.comp K.subtype := by
    ext h
    simp [MulAut.conj_apply]
  have hleft : ((P'.subgroupOf K).map (MulAut.conj c).toMonoidHom).map
      K.subtype = P'.map (MulAut.conj (c : G)).toMonoidHom := by
    calc
      ((P'.subgroupOf K).map (MulAut.conj c).toMonoidHom).map K.subtype
          = (P'.subgroupOf K).map
              (K.subtype.comp (MulAut.conj c).toMonoidHom) := by
              rw [Subgroup.map_map]
      _ = (P'.subgroupOf K).map
              ((MulAut.conj (c : G)).toMonoidHom.comp K.subtype) := by
              rw [hcomm]
      _ = ((P'.subgroupOf K).map K.subtype).map
              (MulAut.conj (c : G)).toMonoidHom := by rw [Subgroup.map_map]
      _ = P'.map (MulAut.conj (c : G)).toMonoidHom := by
        rw [Subgroup.map_subgroupOf_eq_of_le hP'leK]
  have hc2 : P'.map (MulAut.conj (c : G)).toMonoidHom = P := by
    have hmap := congrArg (Subgroup.map K.subtype) hc'
    rw [hleft] at hmap
    have hmap' : (P.subgroupOf K).map K.subtype = P := by
      change (P.subgroupOf (bg.U ⊓ Subgroup.centralizer (V : Set G))).map
        (bg.U ⊓ Subgroup.centralizer (V : Set G)).subtype = P
      exact Subgroup.map_subgroupOf_eq_of_le hPleK
    rw [hmap'] at hmap
    exact hmap
  let m : G := (c : G) * g
  have hmN : m ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hconjm : (MulAut.conj (m : G)).toMonoidHom =
        (MulAut.conj (c : G)).toMonoidHom.comp
          (MulAut.conj g).toMonoidHom := by
      ext x
      change m * x * m⁻¹ = (c : G) * (g * x * g⁻¹) * (c : G)⁻¹
      simp [m]
      group
    calc
      P.map (MulAut.conj m).toMonoidHom
          = P.map ((MulAut.conj (c : G)).toMonoidHom.comp
              (MulAut.conj g).toMonoidHom) := by
              rw [hconjm]
      _ = (P.map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj (c : G)).toMonoidHom := by rw [Subgroup.map_map]
      _ = P'.map (MulAut.conj (c : G)).toMonoidHom := by rfl
      _ = P := hc2
  have hcC : (c : G) ∈ Subgroup.centralizer (V : Set G) :=
    (Subgroup.mem_inf.mp c.2).2
  have hxg : g * x * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hg x).1 hx
  have hconj : m * x * m⁻¹ = g * x * g⁻¹ := by
    calc
      m * x * m⁻¹ = (c : G) * (g * x * g⁻¹) * (c : G)⁻¹ := by
        simp [m]
        group
      _ = g * x * g⁻¹ := by
        have hcomm' := (Subgroup.mem_centralizer_iff.mp hcC)
          (g * x * g⁻¹) hxg
        rw [← hcomm']
        group
  exact ⟨m, hmN, hconj⟩

/-- If `N_G(V)` is transitive on the nonidentity elements of the Klein-four
group `V` and `P` is a Sylow `p`-subgroup of `C_U(V)`, then `N_G(P)` is not
contained in `H = C_G(t)`. -/
public theorem normalizer_sylow_not_le_H
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G)
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    {V P : Subgroup G}
    (hV : IsKleinFour V) (hVmem : bg.t ∈ V)
    (hVtrans : ∀ x y : G, x ∈ V → y ∈ V → x ≠ 1 → y ≠ 1 →
      ∃ n : G, n ∈ Subgroup.normalizer (V : Set G) ∧ n * x * n⁻¹ = y)
    (hPleK : P ≤ Ucentralizer bg V)
    (hPcard : Nat.card P =
      p ^ (Nat.card (Ucentralizer bg V)).factorization p) :
    ¬ Subgroup.normalizer (P : Set G) ≤ bg.H := by
  intro hNPH
  have hy : ∃ y : G, y ∈ V ∧ y ≠ 1 ∧ y ≠ bg.t := by
    by_contra hno
    push Not at hno
    have hle : (V : Set G) ⊆ ({1, bg.t} : Set G) := by
      intro y hy
      by_cases hy1 : y = 1
      · simp [hy1]
      · simp [hno y hy hy1]
    have hcard_le : (V : Set G).ncard ≤ ({1, bg.t} : Set G).ncard :=
      Set.ncard_le_ncard hle
    have hcardV : Nat.card V = (V : Set G).ncard := by
      simpa using (Nat.card_coe_set_eq (V : Set G))
    have h42 : (4 : ℕ) ≤ 2 := by
      have h1 : 4 = (V : Set G).ncard := hV.card_four.symm.trans hcardV
      rw [h1]
      have h2 : ({1, bg.t} : Set G).ncard = 2 :=
        Set.ncard_pair bg.t_involution.1.symm
      exact hcard_le.trans (le_of_eq h2)
    omega
  rcases hy with ⟨y, hyV, hy1, hyt⟩
  obtain ⟨n, hnN, hn⟩ := hVtrans bg.t y hVmem hyV bg.t_involution.1 hy1
  obtain ⟨m, hmN, hm⟩ :=
    frattini_transfer_conj bg p hpodd hVmem hPleK hPcard hVmem hnN
  have hmH : m ∈ bg.H := hNPH hmN
  have hmCent : m ∈ Subgroup.centralizer ({bg.t} : Set G) := by
    rwa [← bg.H_eq_centralizer]
  have hmfix : m * bg.t * m⁻¹ = bg.t := by
    have hcomm : bg.t * m = m * bg.t :=
      (Subgroup.mem_centralizer_singleton_iff.mp hmCent).symm
    calc
      m * bg.t * m⁻¹ = (bg.t * m) * m⁻¹ := by rw [hcomm]
      _ = bg.t := by group
  have hyeq : y = bg.t := by
    calc
      y = n * bg.t * n⁻¹ := hn.symm
      _ = m * bg.t * m⁻¹ := hm.symm
      _ = bg.t := hmfix
  exact hyt hyeq

/-- A Klein-four subgroup containing two distinct nontrivial commuting
involutions is generated by them. -/
private theorem kleinFour_eq_closure_of_commuting_involutions
    {G : Type u} [Group G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b) :
    Subgroup.closure ({a, b} : Set G) =
      firstCaseKleinFourOfCommutingInvolutions a b ha hb hab := by
  apply le_antisymm
  · apply (Subgroup.closure_le
      (K := firstCaseKleinFourOfCommutingInvolutions a b ha hb hab)).2
    intro x hx
    rcases hx with (rfl | rfl) <;>
      simp [firstCaseKleinFourOfCommutingInvolutions]
  · intro x hx
    have hx' : x ∈ ({a * b, a, b, 1} : Set G) := by
      simpa [firstCaseKleinFourOfCommutingInvolutions] using hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    rcases hx' with (rfl | rfl | rfl | rfl)
    · exact (Subgroup.closure {a, b}).mul_mem
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact (Subgroup.closure {a, b}).one_mem

/-- A Klein-four subgroup containing two distinct nontrivial commuting
involutions is generated by them. -/
public theorem kleinFour_eq_closure_of_mem
    {G : Type u} [Group G] [Finite G]
    {V : Subgroup G} (hV : IsKleinFour V)
    {a b : G} (ha : a ∈ V) (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (habne : a ≠ b) (hcomm : Commute a b) :
    V = Subgroup.closure ({a, b} : Set G) := by
  classical
  let : IsKleinFour V := hV
  have haa : a * a = 1 :=
    congrArg Subtype.val (IsKleinFour.mul_self ⟨a, ha⟩)
  have hbb : b * b = 1 :=
    congrArg Subtype.val (IsKleinFour.mul_self ⟨b, hb⟩)
  let K := firstCaseKleinFourOfCommutingInvolutions a b haa hbb hcomm
  have hKleV : K ≤ V := by
    intro x hx
    have hx' : x ∈ ({a * b, a, b, 1} : Set G) := by
      simpa [K, firstCaseKleinFourOfCommutingInvolutions] using hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    rcases hx' with (rfl | rfl | rfl | rfl)
    · exact V.mul_mem ha hb
    · exact ha
    · exact hb
    · exact V.one_mem
  have hcle : Subgroup.closure ({a, b} : Set G) ≤ V :=
    (kleinFour_eq_closure_of_commuting_involutions a b haa hbb hcomm).symm ▸
      hKleV
  have hcard : Nat.card (Subgroup.closure ({a, b} : Set G)) = 4 := by
    rw [kleinFour_eq_closure_of_commuting_involutions a b haa hbb hcomm]
    exact (firstCaseKleinFourOfCommutingInvolutions_isKleinFour
      a b haa hbb ha1 hb1 habne hcomm).card_four
  exact (Subgroup.eq_of_le_of_card_ge hcle
    (hV.card_four.trans hcard.symm).le).symm

/-- `c.U = bg.U` for the first-case data. -/
public theorem firstCase_U_eq_bg_U
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) :
    c.U = d.bg.U := by
  change oddCoreOf c.H = oddCoreOf d.bg.H
  rw [d.H_eq]

public theorem qCoreOf_eq_of_subgroup_eq {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} (h : H = K) (q : ℕ) :
    qCoreOf H q = qCoreOf K q := by
  subst h
  rfl

public theorem prime_ne_two_of_primeCore_ne_bot
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hPne : qCoreOf U p ≠ ⊥) (hUodd : Nat.Coprime 2 (Nat.card U)) :
    p ≠ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  intro hp2
  have hPleU : qCoreOf U p ≤ U := qCoreOf_le U p
  have hPp : IsPGroup p (qCoreOf U p) := qCoreOf_isPGroup U p
  obtain ⟨n, hn⟩ := hPp.exists_card_eq
  have hnpos : 0 < n := by
    by_contra hn0
    have hn0' : n = 0 := Nat.eq_zero_of_not_pos hn0
    have hcard1 : Nat.card (qCoreOf U p) = 1 := by simpa [hn0'] using hn
    exact ((Subgroup.one_lt_card_iff_ne_bot (H := qCoreOf U p)).mpr hPne).ne'
      hcard1
  have hpdvd : p ∣ Nat.card (qCoreOf U p) := by
    rw [hn]
    exact ⟨p ^ (n - 1), by
      rw [show n = (n - 1) + 1 by omega, pow_succ']
      rfl⟩
  have hpdvdU : p ∣ Nat.card U := hpdvd.trans (Subgroup.card_dvd_of_le hPleU)
  rw [hp2] at hpdvdU
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hUodd hpdvdU

public theorem firstCase_oriented_p_odd
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (od : FirstCaseOrientedPrimeData c) :
    od.p ≠ 2 := by
  let : Fintype G := Fintype.ofFinite G
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hq : qCoreOf c.U od.p = qCoreOf od.d.bg.U od.p :=
    qCoreOf_eq_of_subgroup_eq hUeq od.p
  exact prime_ne_two_of_primeCore_ne_bot od.d.bg.U od.p od.p_prime
    (by simpa [hq] using od.primeCore_ne_bot)
    (BenderGlauberman.U_coprime_two od.d.bg)

public theorem firstCase_t2_inverts_primeCore
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (od : FirstCaseOrientedPrimeData c) :
    ∀ x : G, x ∈ qCoreOf od.d.bg.U od.p →
      od.d.bg.t2 * x * od.d.bg.t2⁻¹ = x⁻¹ := by
  intro x hx
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hq : qCoreOf c.U od.p = qCoreOf od.d.bg.U od.p :=
    qCoreOf_eq_of_subgroup_eq hUeq od.p
  have hxI : x ∈ od.d.I2 := by
    simpa [hq] using od.primeCore_le_I2 (by simpa [hq] using hx)
  have hxinv : x ∈ invertedElements c.U od.d.bg.t2 := by
    rw [← od.d.I2_inverted]
    exact hxI
  simpa [hUeq] using hxinv.2

public theorem firstCase_t1_centralizes_primeCore
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (od : FirstCaseOrientedPrimeData c) :
    od.d.bg.t1 ∈ Subgroup.centralizer (qCoreOf od.d.bg.U od.p : Set G) := by
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hq : qCoreOf c.U od.p = qCoreOf od.d.bg.U od.p :=
    qCoreOf_eq_of_subgroup_eq hUeq od.p
  simpa [hq] using od.t1_centralizes

private theorem firstCase_t1_centralizes_primeCore_in_FU
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (od : FirstCaseOrientedPrimeData c) :
    qCoreOf od.d.bg.U od.p ≤
      centralizerIn (fittingSubgroupOf od.d.bg.U) od.d.bg.t1 := by
  intro x hx
  refine ⟨fstar_qCoreOf_le_fittingSubgroupOf od.d.bg.U od.p od.p_prime hx, ?_⟩
  exact (Subgroup.mem_centralizer_singleton_iff).mpr
    ((Subgroup.mem_centralizer_iff.mp
      (firstCase_t1_centralizes_primeCore c od)) x hx)

private theorem firstCase_t1_mem_S_bg
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) :
    d.bg.t1 ∈ (d.bg.S : Subgroup G) :=
  d.bg.t1_mem_S

private theorem firstCase_U_le_centralizer_t
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G) :
    bg.U ≤ Subgroup.centralizer ({bg.t} : Set G) := by
  intro x hx
  have hUleH : bg.U ≤ bg.H := by
    exact le_sup_left.trans (le_of_eq bg.H_eq_US)
  have hxH : x ∈ bg.H := hUleH hx
  rwa [← bg.H_eq_centralizer]

private theorem firstCase_commute_t_ti
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c)
    (fd : FirstCaseFourData c d) :
    Commute c.t d.bg.t2 ∧ Commute c.t d.bg.t1 := by
  let : IsKleinFour fd.V2 := fd.V2_klein
  let : IsKleinFour fd.V1 := fd.V1_klein
  let : IsMulCommutative fd.V2 := IsKleinFour.isMulCommutative
  let : IsMulCommutative fd.V1 := IsKleinFour.isMulCommutative
  constructor
  · have h := congrArg Subtype.val
      (mul_comm' (⟨d.bg.t2, fd.t2_mem_V2⟩ : fd.V2)
        (⟨c.t, fd.t_mem_V2⟩ : fd.V2))
    exact h.symm
  · have h := congrArg Subtype.val
      (mul_comm' (⟨d.bg.t1, fd.t1_mem_V1⟩ : fd.V1)
        (⟨c.t, fd.t_mem_V1⟩ : fd.V1))
    exact h.symm

private theorem firstCase_ti_ne_t
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c)
    (i : Fin 2) : c.t ≠ (if i = 0 then d.bg.t1 else d.bg.t2) := by
  fin_cases i <;> simp
  · intro h
    apply d.bg.t1_not_mem_S0
    rw [← h]
    simpa [d.S0_eq] using c.t_mem_S0
  · intro h
    apply d.bg.t2_not_mem_S0
    rw [← h]
    simpa [d.S0_eq] using c.t_mem_S0

private theorem firstCase_V2_eq_closure
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c)
    (fd : FirstCaseFourData c d) :
    fd.V2 = Subgroup.closure ({c.t, d.bg.t2} : Set G) := by
  have hcomm := (firstCase_commute_t_ti c d fd).1
  have hne : c.t ≠ d.bg.t2 := firstCase_ti_ne_t c d 1
  exact kleinFour_eq_closure_of_mem fd.V2_klein fd.t_mem_V2 fd.t2_mem_V2
    c.t_involution.1 d.bg.t2_involution.1 hne hcomm

private theorem firstCase_V1_eq_closure
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c)
    (fd : FirstCaseFourData c d) :
    fd.V1 = Subgroup.closure ({c.t, d.bg.t1} : Set G) := by
  have hcomm := (firstCase_commute_t_ti c d fd).2
  have hne : c.t ≠ d.bg.t1 := firstCase_ti_ne_t c d 0
  exact kleinFour_eq_closure_of_mem fd.V1_klein fd.t_mem_V1 fd.t1_mem_V1
    c.t_involution.1 d.bg.t1_involution.1 hne hcomm

/-- The Sylow `p`-subgroup `P₂` of `C_U(V₂)` (source notation). -/
public noncomputable def firstCase_P2_sylow
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    Sylow od.p (centralizerIn od.d.bg.U od.d.bg.t2) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fact od.p.Prime := ⟨od.p_prime⟩
  exact centralizerIn_sylow_of_B_of_inverted od.d.bg hU od.d.bg.t2_mem_S od.p
    (BenderGlauberman.U_coprime_two od.d.bg |>.coprime_dvd_right
      (Subgroup.card_dvd_of_le (qCoreOf_le od.d.bg.U od.p)))
    (firstCase_t2_inverts_primeCore c od) Q

/-- The first source assertion `N_G(P₂) ⊄ H`. -/
public theorem firstCase_normalizer_P2_not_le_H
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    ¬ Subgroup.normalizer
        (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ od.d.bg.H := by
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P2s := firstCase_P2_sylow c od hU Q
  let K2 : Subgroup G := od.d.bg.U ⊓
    Subgroup.centralizer (fd.V2 : Set G)
  have hK2eq : centralizerIn od.d.bg.U od.d.bg.t2 = K2 := by
    exact centralizerIn_eq_centralizer_subgroup_of_closure od.d.bg.U
      (firstCase_V2_eq_closure c od.d fd)
      (by simpa [od.d.t_eq] using firstCase_U_le_centralizer_t od.d.bg)
  have hP2 := sylowCarrier_le_and_card P2s hK2eq
  exact normalizer_sylow_not_le_H od.d.bg od.p
    (firstCase_oriented_p_odd c od) fd.V2_klein
    (by simpa [od.d.t_eq] using fd.t_mem_V2)
    (normalizer_transitive_on_kleinFour_pontset hmin c fd.V2_le_S fd.V2_klein)
    hP2.1 hP2.2

/-- The conjugating action of `N_G(V₂)` on `V₂` is realised inside
`N_G(P₂)`, so `N_G(P₂)` is transitive on `V₂#`. -/
public theorem firstCase_P2_transitive
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    ∀ x y : G, x ∈ fd.V2 → y ∈ fd.V2 → x ≠ 1 → y ≠ 1 →
      ∃ m : G,
        m ∈ Subgroup.normalizer
          (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ∧
          m * x * m⁻¹ = y := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P2s := firstCase_P2_sylow c od hU Q
  let K2 : Subgroup G := od.d.bg.U ⊓
    Subgroup.centralizer (fd.V2 : Set G)
  have hK2eq : centralizerIn od.d.bg.U od.d.bg.t2 = K2 :=
    centralizerIn_eq_centralizer_subgroup_of_closure od.d.bg.U
      (firstCase_V2_eq_closure c od.d fd)
      (by simpa [od.d.t_eq] using firstCase_U_le_centralizer_t od.d.bg)
  have hP2 := sylowCarrier_le_and_card P2s hK2eq
  intro x y hxV hyV hx1 hy1
  obtain ⟨g, hgN, hg⟩ :=
    normalizer_transitive_on_kleinFour_pontset hmin c fd.V2_le_S fd.V2_klein
      x y hxV hyV hx1 hy1
  obtain ⟨m, hmN, hm⟩ :=
    frattini_transfer_conj od.d.bg od.p (firstCase_oriented_p_odd c od)
      (by simpa [od.d.t_eq] using fd.t_mem_V2) hP2.1 hP2.2 hxV hgN
  exact ⟨m, hmN, hm.trans hg⟩

/-- The Sylow `p`-subgroup `P₁ = P·P₂` of `C_U(V₁)` (source notation). -/
public noncomputable def firstCase_P1_sylow
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    Sylow od.p (centralizerIn od.d.bg.U od.d.bg.t1) := by
  letI : Fact od.p.Prime := ⟨od.p_prime⟩
  exact centralizerIn_sylow_of_pCore od.d.bg hU od.d.bg.t1_mem_S od.p
    (firstCase_t1_centralizes_primeCore_in_FU c od) Q

/-- The first source assertion `N_G(P₁) ⊄ H`. -/
public theorem firstCase_normalizer_P1_not_le_H
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    ¬ Subgroup.normalizer
        (sylowCarrier (firstCase_P1_sylow c od hU Q) : Set G) ≤ od.d.bg.H := by
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P1s := firstCase_P1_sylow c od hU Q
  let K1 : Subgroup G := od.d.bg.U ⊓
    Subgroup.centralizer (fd.V1 : Set G)
  have hK1eq : centralizerIn od.d.bg.U od.d.bg.t1 = K1 := by
    exact centralizerIn_eq_centralizer_subgroup_of_closure od.d.bg.U
      (firstCase_V1_eq_closure c od.d fd)
      (by simpa [od.d.t_eq] using firstCase_U_le_centralizer_t od.d.bg)
  have hP1 := sylowCarrier_le_and_card P1s hK1eq
  exact normalizer_sylow_not_le_H od.d.bg od.p
    (firstCase_oriented_p_odd c od) fd.V1_klein
    (by simpa [od.d.t_eq] using fd.t_mem_V1)
    (normalizer_transitive_on_kleinFour_pontset hmin c fd.V1_le_S fd.V1_klein)
    hP1.1 hP1.2

/-- The carrier of `P₁ = P·P₂`. -/
public theorem firstCase_P1_carrier
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    sylowCarrier (firstCase_P1_sylow c od hU Q) =
      qCoreOf od.d.bg.U od.p ⊔
        ((Q : Subgroup ↥od.d.bg.B).map od.d.bg.B.subtype) := by
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  simpa [firstCase_P1_sylow] using centralizerIn_sylow_of_pCore_carrier
    od.d.bg hU od.d.bg.t1_mem_S od.p
    (firstCase_t1_centralizes_primeCore_in_FU c od) Q

/-- The carrier of `P₂`. -/
public theorem firstCase_P2_carrier
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    sylowCarrier (firstCase_P2_sylow c od hU Q) =
      (Q : Subgroup ↥od.d.bg.B).map od.d.bg.B.subtype := by
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  simpa [firstCase_P2_sylow, centralizerIn_sylow_of_B_of_inverted] using
    centralizerIn_sylow_of_B_carrier od.d.bg hU od.d.bg.t2_mem_S od.p
      (centralizerIn_fittingSubgroupOf_card_coprime_of_inverted od.d.bg.U
        od.p od.d.bg.t2
        (BenderGlauberman.U_coprime_two od.d.bg |>.coprime_dvd_right
          (Subgroup.card_dvd_of_le (qCoreOf_le od.d.bg.U od.p)))
        (firstCase_t2_inverts_primeCore c od)) Q

/-- First-case normalizer control: `N_G(P) ≤ H` for `P = O_p(U)`. -/
private theorem firstCase_normalizer_P_le_H
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H) :
    Subgroup.normalizer (qCoreOf od.d.bg.U od.p : Set G) ≤ od.d.bg.H := by
  have hPne : qCoreOf od.d.bg.U od.p ≠ ⊥ := by
    have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
    have hq : qCoreOf c.U od.p = qCoreOf od.d.bg.U od.p :=
      qCoreOf_eq_of_subgroup_eq hUeq od.p
    simpa [hq] using od.primeCore_ne_bot
  have hPleFU : qCoreOf od.d.bg.U od.p ≤ fittingSubgroupOf od.d.bg.U :=
    fstar_qCoreOf_le_fittingSubgroupOf od.d.bg.U od.p od.p_prime
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hFU : fittingSubgroupOf c.U = fittingSubgroupOf od.d.bg.U :=
    congrArg fittingSubgroupOf hUeq
  have hPleFU' : qCoreOf od.d.bg.U od.p ≤ c.FU := by
    simpa [CentralizerSetup.FU, hFU] using hPleFU
  have hNX : Subgroup.normalizer (qCoreOf od.d.bg.U od.p : Set G) ≤ c.Hhat :=
    hfirst.2 (qCoreOf od.d.bg.U od.p) hPne hPleFU'
  have hNXH : Subgroup.normalizer (qCoreOf od.d.bg.U od.p : Set G) ≤ c.H := by
    simpa [hHhat] using hNX
  simpa [od.d.H_eq] using hNXH

/-- The source assertion `P₁ ≠ P`. -/
public theorem firstCase_P1_ne_P
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    sylowCarrier (firstCase_P1_sylow c od hU Q) ≠ qCoreOf od.d.bg.U od.p := by
  intro hP1eq
  let fd := Classical.choice (exists_firstCaseFourData c od.d)
  have hNP1 : Subgroup.normalizer
      (sylowCarrier (firstCase_P1_sylow c od hU Q) : Set G) ≤ od.d.bg.H := by
    rw [hP1eq]
    exact firstCase_normalizer_P_le_H c od hfirst hHhat
  exact (firstCase_normalizer_P1_not_le_H hmin c od fd hU Q) hNP1

/-- The source assertion `P₂ ≠ 1`. -/
public theorem firstCase_P2_ne_one
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    sylowCarrier (firstCase_P2_sylow c od hU Q) ≠ ⊥ := by
  intro hP2bot
  let fd := Classical.choice (exists_firstCaseFourData c od.d)
  have hP1eq : sylowCarrier (firstCase_P1_sylow c od hU Q) =
      qCoreOf od.d.bg.U od.p := by
    rw [firstCase_P1_carrier c od hU Q]
    have hP2c : (Q : Subgroup ↥od.d.bg.B).map od.d.bg.B.subtype = ⊥ := by
      rw [← firstCase_P2_carrier c od hU Q]
      exact hP2bot
    rw [hP2c, sup_bot_eq]
  have hNP1 : Subgroup.normalizer
      (sylowCarrier (firstCase_P1_sylow c od hU Q) : Set G) ≤ od.d.bg.H := by
    rw [hP1eq]
    exact firstCase_normalizer_P_le_H c od hfirst hHhat
  exact (firstCase_normalizer_P1_not_le_H hmin c od fd hU Q) hNP1

end CFSG.GorensteinWalter
