module

public import CFSG.Quasithin.Background.C124L2MP
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem burnsideB610_exists_two_odd (g : G) :
    ∃ a ∈ Subgroup.zpowers g, ∃ b ∈ Subgroup.zpowers g, g = a * b ∧
      (∃ k : ℕ, a ^ 2 ^ k = 1) ∧ Odd (orderOf b) := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have hgcd := Nat.gcd_eq_gcd_ab (2 ^ k) m
  rw [hcop.gcd_eq_one] at hgcd
  set u := Nat.gcdA (2 ^ k) m with hu
  set v := Nat.gcdB (2 ^ k) m with hv
  refine ⟨g ^ (v * (m : ℤ)), Subgroup.zpow_mem_zpowers g _,
    g ^ (u * ((2 ^ k : ℕ) : ℤ)), Subgroup.zpow_mem_zpowers g _, ?_, ⟨k, ?_⟩, ?_⟩
  · rw [← zpow_add, add_comm]
    have : u * ((2 ^ k : ℕ) : ℤ) + v * (m : ℤ) = 1 := by
      rw [mul_comm u, mul_comm v]
      exact hgcd.symm
    rw [this, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul]
    have : v * (m : ℤ) * ((2 ^ k : ℕ) : ℤ) = (orderOf g : ℤ) * v := by
      rw [hn]
      push_cast
      ring
    rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · have hb : (g ^ (u * ((2 ^ k : ℕ) : ℤ))) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : u * ((2 ^ k : ℕ) : ℤ) * (m : ℤ) = (orderOf g : ℤ) * u := by
        rw [hn]
        push_cast
        ring
      rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hb)

theorem burnsideB610_le_of_isSylowTwoOf_normal {C Q P : Subgroup G} (hQC : IsSylowTwoOf Q C)
    (hCQ : C ≤ Subgroup.normalizer (Q : Set G)) (hPC : P ≤ C) (hP : IsPGroup 2 P) : P ≤ Q := by
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := hPC.trans hCQ
  have h2 : IsPGroup 2 ↥(P ⊔ Q) := hP.to_sup_of_normal_right' hQC.2.1 hPQ
  have hQPQ : Q ≤ P ⊔ Q := le_sup_right
  have hPQC : P ⊔ Q ≤ C := sup_le hPC hQC.1
  have hmul := Subgroup.relIndex_mul_relIndex Q (P ⊔ Q) C hQPQ hPQC
  have hodd : ¬ 2 ∣ Q.relIndex (P ⊔ Q) := fun hd =>
    hQC.2.2 (by
      have : Q.relIndex C = (Q.subgroupOf C).index := rfl
      rw [← this, ← hmul]
      exact hd.mul_right _)
  have hpow : ∃ n : ℕ, Q.relIndex (P ⊔ Q) = 2 ^ n := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h2
    have hdvd : Q.relIndex (P ⊔ Q) ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.relIndex_dvd_card Q (P ⊔ Q)
    exact (Nat.dvd_prime_pow Nat.prime_two).1 hdvd |>.imp fun _ h => h.2
  obtain ⟨n, hn⟩ := hpow
  have h1 : Q.relIndex (P ⊔ Q) = 1 := by
    rcases n with _ | n
    · simpa using hn
    · exact absurd (hn ▸ dvd_pow_self 2 (Nat.succ_ne_zero n)) hodd
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.1 h1)

theorem burnsideB610_mem_pCoreOf_of_two {H T M V : Subgroup G} (hMP : MinParabolic H T M)
    (hred : IsTwoReducedIn H V) (hHV : ¬ H ≤ Subgroup.centralizer (V : Set G)) {c : G}
    (hcH : c ∈ H) (hcV : c ∈ Subgroup.centralizer (V : Set G)) (hc2 : ∃ k : ℕ, c ^ 2 ^ k = 1) :
    c ∈ pCoreOf 2 H := by
  set C := H ⊓ Subgroup.centralizer (V : Set G) with hC
  have hQC : pCoreOf 2 H ≤ C :=
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 H) (MinParabolic.pCoreOf_le_centralizer hred)
  have hCM : C ≤ M := (hMP.inf_centralizer_le_kerIn hred hHV).trans kerIn_le
  have hCn : H ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer hred.2.1 hg⟩
  have hsyl : IsSylowTwoOf (pCoreOf 2 H) C := by
    have h1 := (hMP.le_kerIn_and_isSylowTwoOf_of_le hCn hCM).2
    rwa [inf_eq_left.mpr hQC] at h1
  have hCQ : C ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hzC : Subgroup.zpowers c ≤ C := Subgroup.zpowers_le.mpr ⟨hcH, hcV⟩
  have hz2 : IsPGroup 2 (Subgroup.zpowers c) := by
    obtain ⟨k, hk⟩ := hc2
    rintro ⟨x, hx⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨k, Subtype.ext ?_⟩
    show (c ^ j) ^ 2 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  exact burnsideB610_le_of_isSylowTwoOf_normal hsyl hCQ hzC hz2 (Subgroup.mem_zpowers c)

theorem burnsideB610_map_conj_mul_of_mem_normalizer {S : Subgroup G} {x a : G}
    (ha : a ∈ Subgroup.normalizer (S : Set G)) :
    S.map (MulAut.conj (x * a)).toMonoidHom = S.map (MulAut.conj x).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨a * s * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha s).mp hs, by group⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨a⁻¹ * s * a, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S : Set G)).inv_mem ha) s).mp hs
    simpa using this

theorem burnsideB610_join_le_join_twoResidual {H T M V L : Subgroup G} (hMP : MinParabolic H T M)
    (hred : IsTwoReducedIn H V) (hHV : ¬ H ≤ Subgroup.centralizer (V : Set G)) (hLH : L ≤ H)
    (hLres : L ≤ twoResidual L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))) :
    (⨆ l ∈ L, (baum T).map (MulAut.conj l).toMonoidHom) ≤
      ⨆ l ∈ twoResidual L, (baum T).map (MulAut.conj l).toMonoidHom := by
  have hT := hMP.isSylow
  have hTS : T ≤ Subgroup.normalizer (baum T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hL₁L : twoResidual L ≤ L := twoResidual_le L
  have hCn : twoResidual L ≤ Subgroup.normalizer
      ((H ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hLH (hL₁L hg)), B6.le_normalizer_centralizer hred.2.1 (hLH (hL₁L hg))⟩
  refine iSup₂_le fun l hl => ?_
  have hl' : l ∈ ((twoResidual L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)) : Subgroup G) :
      Set G) := hLres hl
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCn] at hl'
  obtain ⟨l₁, hl₁, c, hc, rfl⟩ := hl'
  have hcL : c ∈ L := by
    have := L.mul_mem (L.inv_mem (hL₁L hl₁)) hl
    simpa using this
  obtain ⟨a, ha, b, hb, hab, ha2, hbodd⟩ := burnsideB610_exists_two_odd c
  have hzL : Subgroup.zpowers c ≤ L := Subgroup.zpowers_le.mpr hcL
  have hzC : Subgroup.zpowers c ≤ H ⊓ Subgroup.centralizer (V : Set G) :=
    Subgroup.zpowers_le.mpr hc
  have haQ : a ∈ pCoreOf 2 H :=
    burnsideB610_mem_pCoreOf_of_two hMP hred hHV (hzC ha).1 (hzC ha).2 ha2
  have hbL₁ : b ∈ twoResidual L := F6.mem_twoResidual_of_odd (hzL hb) hbodd
  have hcomm : a * b = b * a := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_add, ← zpow_add, add_comm]
  have he : (l₁ * c : G) = (l₁ * b) * a := by rw [hab, hcomm, mul_assoc]
  beta_reduce
  rw [he, burnsideB610_map_conj_mul_of_mem_normalizer (hTS (hQT haQ))]
  exact le_iSup₂_of_le (f := fun l (_ : l ∈ twoResidual L) =>
    (baum T).map (MulAut.conj l).toMonoidHom) (l₁ * b) ((twoResidual L).mul_mem hl₁ hbL₁) le_rfl

theorem burnsideB610_le_of_isSylowTwoOf_of_le {A P B : Subgroup G} (hA : IsSylowTwoOf A B)
    (hAP : A ≤ P) (hPB : P ≤ B) (hP : IsPGroup 2 P) : P ≤ A := by
  have hmul := Subgroup.relIndex_mul_relIndex A P B hAP hPB
  have hodd : ¬ 2 ∣ A.relIndex P := fun hd =>
    hA.2.2 (by
      have : A.relIndex B = (A.subgroupOf B).index := rfl
      rw [← this, ← hmul]
      exact hd.mul_right _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : A.relIndex P ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.relIndex_dvd_card A P
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have h1 : A.relIndex P = 1 := by
    rcases j with _ | j
    · simpa using hj
    · exact absurd (hj ▸ dvd_pow_self 2 (Nat.succ_ne_zero j)) hodd
  exact Subgroup.relIndex_eq_one.1 h1

theorem burnsideB610_isSylowTwoOf_join {H T M V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMP : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hHV : ¬ H ≤ Subgroup.centralizer (V : Set G)) (hLH : L ≤ H)
    (hLres : L ≤ twoResidual L ⊔ (H ⊓ Subgroup.centralizer (V : Set G)))
    (hE : omegaOneCenterOf (thompsonJ T) ≤ (V ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
      (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual L : Set G)))
    (hSN : autI hV (baum T) ≤ Subgroup.normalizer (autI hV L : Set (MulAut (IntMod V hV))))
    (hsyl : IsSylowTwoOf (autI hV (baum T) ⊓ autI hV L) (autI hV L)) :
    IsSylowTwoOf (baum T) (⨆ l ∈ L, (baum T).map (MulAut.conj l).toMonoidHom) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := baum T with hSdef
  set E := omegaOneCenterOf (thompsonJ T) with hEdef
  set Y := ⨆ l ∈ L, S.map (MulAut.conj l).toMonoidHom with hYdef
  have hT := hMP.isSylow
  have hST : S ≤ T := inf_le_left
  have hS2 : IsPGroup 2 S := hT.2.1.to_le hST
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hTH : T ≤ H := hT.1
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hQC : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G) :=
    MinParabolic.pCoreOf_le_centralizer hred
  have hSY : S ≤ Y := by
    have h1 := le_iSup₂_of_le (f := fun l (_ : l ∈ L) => S.map (MulAut.conj l).toMonoidHom)
      (1 : G) L.one_mem le_rfl
    intro s hs
    refine h1 ⟨s, hs, ?_⟩
    simp
  have hYLS : Y ≤ L ⊔ S := by
    refine iSup₂_le fun l hl => ?_
    rintro _ ⟨s, hs, rfl⟩
    show l * s * l⁻¹ ∈ L ⊔ S
    exact (L ⊔ S).mul_mem ((L ⊔ S).mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hs))
      ((L ⊔ S).inv_mem (Subgroup.mem_sup_left hl))
  have hLSH : L ⊔ S ≤ H := sup_le hLH (hST.trans hTH)
  have hY₁ := burnsideB610_join_le_join_twoResidual (T := T) hMP hred hHV hLH hLres
  have hY₁cent : (⨆ l ∈ twoResidual L, S.map (MulAut.conj l).toMonoidHom) ≤
      Subgroup.centralizer
        ((E ⊓ Subgroup.centralizer (twoResidual L : Set G) : Subgroup G) : Set G) := by
    refine iSup₂_le fun l hl => ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro e ⟨heE, heL⟩
    have hel : l * e = e * l := Subgroup.mem_centralizer_iff.mp heL l hl
    have hes : e * s = s * e := Subgroup.mem_centralizer_iff.mp hs.2 e heE
    show e * (l * s * l⁻¹) = (l * s * l⁻¹) * e
    have hel' : e * l⁻¹ = l⁻¹ * e := by
      calc e * l⁻¹ = l⁻¹ * (l * e) * l⁻¹ := by group
        _ = l⁻¹ * (e * l) * l⁻¹ := by rw [hel]
        _ = l⁻¹ * e := by group
    calc e * (l * s * l⁻¹) = (e * l) * s * l⁻¹ := by group
      _ = l * (e * s) * l⁻¹ := by rw [← hel]; group
      _ = l * s * (e * l⁻¹) := by rw [hes]; group
      _ = l * s * l⁻¹ * e := by rw [hel']; group
  have hYQ : ∀ x ∈ Y, x ∈ pCoreOf 2 H → x ∈ S := by
    intro x hxY hxQ
    refine ⟨hQT hxQ, ?_⟩
    show x ∈ Subgroup.centralizer (E : Set G)
    have hxc := hY₁cent (hY₁ hxY)
    have hle : (V ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
        (E ⊓ Subgroup.centralizer (twoResidual L : Set G)) ≤
          Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (Subgroup.mem_centralizer_iff.mp (hQC hxQ) y hy.1).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (Subgroup.mem_centralizer_iff.mp hxc y hy).symm
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h1 := Subgroup.mem_centralizer_iff.mp (hle (hE he)) x rfl
    exact h1.symm
  have hSN' : S ≤ Subgroup.normalizer (V : Set G) := hST.trans (hTH.trans hHN)
  have hS2' : IsPGroup 2 (autI hV S) := B2F.isPGroup_autI hV hS2 hSN'
  have hSL : IsSylowTwoOf (autI hV S) (autI hV L ⊔ autI hV S) :=
    C124.L2.isSylowTwoOf_sup_of_normalizing hSN hS2' hsyl
  have hSsub : IsPGroup 2 (S.subgroupOf Y) := hS2.comap_of_injective Y.subtype Y.subtype_injective
  obtain ⟨P', hP'⟩ := hSsub.exists_le_sylow
  set P : Subgroup G := (P' : Subgroup ↥Y).map Y.subtype with hPdef
  have hPY : P ≤ Y := Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 P := P'.isPGroup'.map Y.subtype
  have hSP : S ≤ P := by
    intro s hs
    exact ⟨⟨s, hSY hs⟩, hP' (Subgroup.mem_subgroupOf.mpr hs), rfl⟩
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPY.trans (hYLS.trans (hLSH.trans hHN))
  have hPaut : autI hV P ≤ autI hV S := by
    have hle1 : autI hV P ≤ autI hV L ⊔ autI hV S := by
      rw [← autI_sup hV (hLH.trans hHN) hSN']
      exact autI_mono hV (hPY.trans hYLS)
    exact burnsideB610_le_of_isSylowTwoOf_of_le hSL (autI_mono hV hSP) hle1
      (B2F.isPGroup_autI hV hP2 hPN)
  have hPS : P ≤ S := by
    intro x hxP
    have hxN := hPN hxP
    obtain ⟨s, hsS, hs⟩ := (mem_autI hV).1 (hPaut (convI_mem_autI hV hxP hxN))
    have hc : (s : G)⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
      have h1 : convI hV (s⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hs, inv_mul_cancel]
      have := (convI_eq_one_iff hV _).1 h1
      simpa using this
    have hcP : (s : G)⁻¹ * x ∈ P := P.mul_mem (P.inv_mem (hSP hsS)) hxP
    have hcH : (s : G)⁻¹ * x ∈ H := (hPY.trans (hYLS.trans hLSH)) hcP
    have hcQ : (s : G)⁻¹ * x ∈ pCoreOf 2 H := by
      refine burnsideB610_mem_pCoreOf_of_two hMP hred hHV hcH hc ?_
      obtain ⟨k, hk⟩ := hP2 ⟨_, hcP⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hcS := hYQ _ (hPY hcP) hcQ
    have : x = (s : G) * ((s : G)⁻¹ * x) := by group
    rw [this]
    exact S.mul_mem hsS hcS
  have hPeq : P = S := le_antisymm hPS hSP
  have hP'eq : (P' : Subgroup ↥Y) = S.subgroupOf Y := by
    rw [Subgroup.subgroupOf, ← hPeq, hPdef,
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
  refine ⟨hSY, hS2, ?_⟩
  rw [← hP'eq]
  exact P'.not_dvd_index

end CFSG.Quasithin
