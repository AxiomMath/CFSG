module

public import CFSG.RankThree.GF2n.Tim77.Cor2BetaBasic
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions CFSG.Open Subgroup
open CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem cor2Beta_components_commute {H K L : Subgroup G} (hK : IsComponentOf K H)
    (hL : IsComponentOf L H) (hne : K ≠ L) : ∀ x ∈ K, ∀ y ∈ L, x * y = y * x := by
  have hK' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hK.1).mp (CFSG.Assembly.isComponentOf_iff_open.mpr hK)
  have hL' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hL.1).mp (CFSG.Assembly.isComponentOf_iff_open.mpr hL)
  rcases CFSG.LocalCores.distinct_components_commute hK' hL' with h | h
  · exfalso
    apply hne
    have := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hK.1, inf_eq_left.mpr hL.1] at this
  · intro x hx y hy
    have h1 := Subgroup.commutator_mem_commutator
      (show (⟨x, hK.1 hx⟩ : ↥H) ∈ K.subgroupOf H from hx)
      (show (⟨y, hL.1 hy⟩ : ↥H) ∈ L.subgroupOf H from hy)
    rw [h, Subgroup.mem_bot] at h1
    have h2 : x * y * x⁻¹ * y⁻¹ = 1 := by
      have := congrArg Subtype.val h1
      simpa [commutatorElement_def] using this
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h2, one_mul]

theorem cor2Beta_inner_on_layer_of_components {H E : Subgroup G}
    (hE : E = sSup {K : Subgroup G | IsComponentOf K H}) {a : G}
    (h : ∀ K : Subgroup G, IsComponentOf K H → ∃ k ∈ K, ∀ x ∈ K, a * x * a⁻¹ = k * x * k⁻¹) :
    ∃ e ∈ E, ∀ x ∈ E, a * x * a⁻¹ = e * x * e⁻¹ := by
  classical
  choose! k hkK hk using h
  have hfin : {K : Subgroup G | IsComponentOf K H}.Finite := Set.toFinite _
  set s : Finset (Subgroup G) := hfin.toFinset with hs
  have hmem : ∀ K, K ∈ s ↔ IsComponentOf K H := fun K => by simp [hs]
  have hcomm : (s : Set (Subgroup G)).Pairwise (fun K L => Commute (k K) (k L)) := by
    intro K hK L hL hKL
    exact cor2Beta_components_commute ((hmem K).mp hK) ((hmem L).mp hL) hKL _
      (hkK K ((hmem K).mp hK)) _ (hkK L ((hmem L).mp hL))
  let e : G := s.noncommProd k hcomm
  have heE : e ∈ E := by
    rw [hE]
    exact Subgroup.noncommProd_mem _ hcomm fun K hK =>
      le_sSup (show K ∈ {K : Subgroup G | IsComponentOf K H} from (hmem K).mp hK)
        (hkK K ((hmem K).mp hK))
  refine ⟨e, heE, ?_⟩
  have hsub : E ≤ Subgroup.centralizer ({e⁻¹ * a} : Set G) := by
    rw [hE]
    refine sSup_le fun K hK x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hKs : K ∈ s := (hmem K).mpr hK
    have hprod := Finset.mul_noncommProd_erase s hKs k hcomm
    have hcx : (s.erase K).noncommProd k
        (fun _ hx _ hy hxy => hcomm (s.mem_of_mem_erase hx) (s.mem_of_mem_erase hy) hxy)
        ∈ Subgroup.centralizer ({x} : Set G) := by
      refine Subgroup.noncommProd_mem _ _ fun L hL => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hLK : L ≠ K := Finset.ne_of_mem_erase hL
      exact (cor2Beta_components_commute ((hmem K).mp hKs) ((hmem L).mp (s.mem_of_mem_erase hL))
        hLK.symm x hx _ (hkK L ((hmem L).mp (s.mem_of_mem_erase hL)))).symm
    set e' := (s.erase K).noncommProd k
        (fun _ hx _ hy hxy => hcomm (s.mem_of_mem_erase hx) (s.mem_of_mem_erase hy) hxy) with he'
    have hxe' : e' * x = x * e' := Subgroup.mem_centralizer_singleton_iff.mp hcx
    have hee : e = k K * e' := hprod.symm
    have h1 := hk K hK x hx
    have h2 : e * x * e⁻¹ = k K * x * (k K)⁻¹ := by
      rw [hee]
      calc k K * e' * x * (k K * e')⁻¹ = k K * (e' * x * e'⁻¹) * (k K)⁻¹ := by group
        _ = k K * x * (k K)⁻¹ := by rw [hxe']; group
    have h3 : a * x * a⁻¹ = e * x * e⁻¹ := by rw [h1, h2]
    calc x * (e⁻¹ * a) = e⁻¹ * (e * x * e⁻¹) * a := by group
      _ = e⁻¹ * (a * x * a⁻¹) * a := by rw [h3]
      _ = (e⁻¹ * a) * x := by group
  intro x hx
  have := Subgroup.mem_centralizer_singleton_iff.mp (hsub hx)
  calc a * x * a⁻¹ = e * (e⁻¹ * a * x) * a⁻¹ := by group
    _ = e * (x * (e⁻¹ * a)) * a⁻¹ := by rw [this]
    _ = e * x * e⁻¹ := by group

theorem cor2Beta_le_of_odd_normal {Y : Type} [Group Y] [Finite Y] {O M : Subgroup Y} [O.Normal]
    (hOp : IsPGroup 2 (Y ⧸ O)) (hM : Odd (Nat.card M)) : M ≤ O := by
  intro z hz
  obtain ⟨k, hk⟩ := hOp (QuotientGroup.mk z)
  have h1 : orderOf (QuotientGroup.mk z : Y ⧸ O) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (QuotientGroup.mk z : Y ⧸ O) ∣ Nat.card M :=
    (orderOf_map_dvd (QuotientGroup.mk' O) z).trans (Subgroup.orderOf_dvd_natCard M hz)
  have h3 : Nat.Coprime (orderOf (QuotientGroup.mk z : Y ⧸ O)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_left h2 hM.coprime_two_right)
  have h4 : orderOf (QuotientGroup.mk z : Y ⧸ O) = 1 := Nat.Coprime.eq_one_of_dvd h3 h1
  exact (QuotientGroup.eq_one_iff z).mp (orderOf_eq_one_iff.mp h4)

theorem cor2Beta_decomp_Y_commute {S : Sylow 2 G} {t : G} (hs : ShultSetup S t) {E Y : Subgroup G}
    (hd : Cor2BetaDecomp (normalClosure ({t} : Set G)) E Y)
    (hO : ∀ N : Subgroup G, N.Normal → N ≤ normalClosure ({t} : Set G) → Odd (Nat.card N) →
      ∀ n ∈ N, ∀ h ∈ normalClosure ({t} : Set G), n * h = h * n) :
    ∀ y ∈ Y, ∀ h ∈ normalClosure ({t} : Set G), y * h = h * y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := normalClosure ({t} : Set G) with hH
  have hHn : H.Normal := inferInstance
  have htH : t ∈ H := subset_normalClosure (Set.mem_singleton t)
  haveI hYn : Y.Normal := hd.Y_normal
  haveI hEn : E.Normal := hd.E_normal
  obtain ⟨O, hOn, hOodd, hO2, hOp⟩ := hd.Y_compl
  haveI := hOn
  set O' : Subgroup G := O.map Y.subtype with hO'
  have hO'Y : O' ≤ Y := by
    rintro _ ⟨o, -, rfl⟩
    exact o.2
  have hO'odd : Odd (Nat.card O') := by
    rw [hO', Subgroup.card_map_of_injective Y.subtype_injective]
    exact hOodd
  have hO'n : O'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨o, ho, rfl⟩ := hn
    let φ : MulAut ↥Y := MulAut.conjNormal g
    have hM : (O.map φ.toMonoidHom).Normal := hOn.map _ φ.surjective
    have hModd : Odd (Nat.card (O.map φ.toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
      exact hOodd
    have hle := cor2Beta_le_of_odd_normal (O := O) hOp hModd
    have hmem : φ o ∈ O := hle ⟨o, ho, rfl⟩
    exact ⟨φ o, hmem, rfl⟩
  have hO'c : ∀ o ∈ O', ∀ h ∈ H, o * h = h * o :=
    hO O' hO'n (hO'Y.trans hd.Y_le) hO'odd
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal S (N := Y)
  have hsup : O ⊔ (P : Subgroup ↥Y) = ⊤ := by
    have h1 : (O ⊔ (P : Subgroup ↥Y)).index ∣ (P : Subgroup ↥Y).index :=
      Subgroup.index_dvd_of_le le_sup_right
    have h2 : (O ⊔ (P : Subgroup ↥Y)).index ∣ O.index := Subgroup.index_dvd_of_le le_sup_left
    obtain ⟨k, hk⟩ := hOp.exists_card_eq
    have hOi : O.index = 2 ^ k := by rw [Subgroup.index_eq_card, hk]
    have hd2 : ¬ 2 ∣ (O ⊔ (P : Subgroup ↥Y)).index := fun h => P.not_dvd_index (h.trans h1)
    have hc : Nat.Coprime ((O ⊔ (P : Subgroup ↥Y)).index) (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hd2).symm
    have h3 : (O ⊔ (P : Subgroup ↥Y)).index = 1 := Nat.Coprime.eq_one_of_dvd hc (hOi ▸ h2)
    exact Subgroup.index_eq_one.mp h3
  obtain ⟨e, he, y₀, hy₀, hey⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (hd.sup_eq ▸ htH)
  have hy₀P : ∀ p ∈ (S : Subgroup G), p ∈ Y → p * y₀ = y₀ * p := by
    intro p hpS hpY
    have h1 : p * t = t * p := hs.central p hpS
    have h2 : e * p = p * e := hd.comm e he p hpY
    rw [← hey] at h1
    have h3 : e * (p * y₀) = e * (y₀ * p) := by
      calc e * (p * y₀) = (e * p) * y₀ := by group
        _ = (p * e) * y₀ := by rw [h2]
        _ = p * (e * y₀) := by group
        _ = (e * y₀) * p := h1
        _ = e * (y₀ * p) := by group
    exact mul_left_cancel h3
  have hy₀Y : ∀ y' ∈ Y, y₀ * y' = y' * y₀ := by
    intro y' hy'
    obtain ⟨o, ho, p, hp, hop⟩ :=
      Subgroup.mem_sup_of_normal_left.mp (hsup ▸ Subgroup.mem_top (⟨y', hy'⟩ : ↥Y))
    have hy'eq : y' = (o : G) * (p : G) := by
      have := congrArg Subtype.val hop
      simpa using this.symm
    have hoO' : (o : G) ∈ O' := ⟨o, ho, rfl⟩
    have hpS : (p : G) ∈ (S : Subgroup G) := by
      have : p ∈ (P : Subgroup ↥Y) := hp
      rw [hP] at this
      exact (Subgroup.mem_inf.mp this).1
    have hpY : (p : G) ∈ Y := p.2
    have hoc := hO'c _ hoO' y₀ (hd.Y_le hy₀)
    have hpc := hy₀P _ hpS hpY
    rw [hy'eq]
    calc y₀ * ((o : G) * (p : G)) = (y₀ * (o : G)) * (p : G) := by group
      _ = ((o : G) * y₀) * (p : G) := by rw [← hoc]
      _ = (o : G) * (y₀ * (p : G)) := by group
      _ = (o : G) * ((p : G) * y₀) := by rw [hpc]
      _ = ((o : G) * (p : G)) * y₀ := by group
  have hy₀H : ∀ h ∈ H, y₀ * h = h * y₀ := by
    have hsub : E ⊔ Y ≤ Subgroup.centralizer ({y₀} : Set G) :=
      sup_le (fun x hx => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hd.comm x hx y₀ hy₀)
        (fun y' hy' => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hy₀Y y' hy').symm)
    intro h hh
    have := Subgroup.mem_centralizer_singleton_iff.mp (hsub (hd.sup_eq ▸ hh))
    exact this.symm
  let Z : Subgroup G := Subgroup.centralizer (H : Set G) ⊓ H
  have hZn : Z.Normal := by
    refine ⟨fun z hz g => ?_⟩
    obtain ⟨hzc, hzH⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨?_, hHn.conj_mem z hzH g⟩
    rw [Subgroup.mem_centralizer_iff] at hzc ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ H := by simpa using hHn.conj_mem x hx g⁻¹
    have := hzc _ hx'
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = (g * z * g⁻¹) * x := by group
  have hy₀Z : y₀ ∈ Z :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun h hh => (hy₀H h hh).symm,
      hd.Y_le hy₀⟩
  have htN : t ∈ E ⊔ Z := hey ▸ Subgroup.mul_mem_sup he hy₀Z
  have hHle : H ≤ E ⊔ Z := Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr htN)
  intro y hy h hh
  obtain ⟨e', he', z, hz, hyez⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (hHle (hd.Y_le hy))
  obtain ⟨hzc, hzH⟩ := Subgroup.mem_inf.mp hz
  have hzc' := Subgroup.mem_centralizer_iff.mp hzc
  have he'E : ∀ x ∈ E, e' * x = x * e' := by
    intro x hx
    have hx1 : x * y = y * x := hd.comm x hx y hy
    have hx2 : x * z = z * x := hzc' x (hd.E_le hx)
    have : e' = y * z⁻¹ := by rw [← hyez]; group
    rw [this]
    calc y * z⁻¹ * x = y * (z⁻¹ * x) := by group
      _ = y * (x * z⁻¹) :=
          congrArg (y * ·) (Commute.inv_right (show Commute x z from hx2)).eq.symm
      _ = (y * x) * z⁻¹ := by group
      _ = (x * y) * z⁻¹ := by rw [hx1]
      _ = x * (y * z⁻¹) := by group
  have he'Y : ∀ y'' ∈ Y, e' * y'' = y'' * e' := fun y'' hy'' => hd.comm e' he' y'' hy''
  have he'H : e' * h = h * e' := by
    have hsub : E ⊔ Y ≤ Subgroup.centralizer ({e'} : Set G) :=
      sup_le (fun x hx => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (he'E x hx).symm)
        (fun y'' hy'' => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (he'Y y'' hy'').symm)
    have := Subgroup.mem_centralizer_singleton_iff.mp (hsub (hd.sup_eq ▸ hh))
    exact this.symm
  have hzh : z * h = h * z := (hzc' h hh).symm
  calc y * h = (e' * z) * h := by rw [hyez]
    _ = e' * (z * h) := by group
    _ = e' * (h * z) := by rw [hzh]
    _ = (e' * h) * z := by group
    _ = (h * e') * z := by rw [he'H]
    _ = h * (e' * z) := by group
    _ = h * y := by rw [hyez]

end CFSG.RankThree.GF2n.Tim77
