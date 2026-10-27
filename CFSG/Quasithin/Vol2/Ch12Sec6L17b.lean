module

public import CFSG.Quasithin.Vol2.Ch12Sec6L17a
public import CFSG.Quasithin.Vol2.Ch12Sec6L14b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace S126T2

section Index

variable {G : Type} [Group G] [Finite G]

theorem relIndex_autOn_eq {U H K : Subgroup G} (hHK : H ≤ K)
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hC : K ⊓ Subgroup.centralizer (U : Set G) ≤ H) :
    (autOn H U).relIndex (autOn K U) = H.relIndex K :=
  CFSG.Quasithin.relIndex_autOn hHK hKU hC

end Index

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem autOn_le_centralizerSection (hD2 : Lemma12_6_4_5) {F : Frame126 T L V} {v : G}
    {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) :
    autOn (Rsec L Kv S v) (Usec Kv S) ≤ centralizerSection (autOn S (Usec Kv S))
      (autOn (Lv L v) (Usec Kv S)) (pCoreOf 2 (autOn (Lv L v) (Usec Kv S))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, -, hReq⟩ := hD2 G T L V F v Kv S hC
  set U := Usec Kv S with hU
  have hXU : Kv ⊔ S ≤ Subgroup.normalizer (U : Set G) :=
    (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_Usec Kv S)
  have hSU : S ≤ Subgroup.normalizer (U : Set G) := (le_sup_right : S ≤ Kv ⊔ S).trans hXU
  have hRS : Rsec L Kv S v ≤ S := by rw [hReq]; exact centralizerSection_le_left _ _ _
  intro ρ hρ
  obtain ⟨⟨r, hrN⟩, hrR, rfl⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 hρ
  have hrc : r ∈ centralizerSection S (Lv L v) (pCoreOf 2 (Lv L v)) := hReq ▸ hrR
  obtain ⟨-, hrL, -, hrcomm⟩ := hrc
  set ρr := conjAct U ⟨r, hrN⟩ with hρr
  have hρS : ρr ∈ autOn S U := QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨r, hrN⟩, hRS hrR, rfl⟩
  have hρZ : ρr ∈ autOn (Subgroup.zpowers r) U :=
    QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨r, hrN⟩, Subgroup.mem_zpowers r, rfl⟩
  have hρN : ρr ∈ Subgroup.normalizer (autOn (Lv L v) U : Set (MulAut ↥U)) :=
    autOn_le_normalizer ((Subgroup.zpowers_le).2 hrL) hρZ
  refine ⟨hρS, hρN, normalizer_le_normalizer_pCoreOf 2 _ hρN, fun b hb => ?_⟩
  obtain ⟨⟨l, hlN⟩, hlL, rfl⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 hb
  have hlr := hrcomm l hlL
  have hc : l * r * l⁻¹ * r⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hrN)
      (Subgroup.inv_mem _ hlN)) (Subgroup.inv_mem _ hrN)
  have he : conjAct U ⟨l, hlN⟩ * ρr * (conjAct U ⟨l, hlN⟩)⁻¹ * ρr⁻¹ =
      conjAct U ⟨l * r * l⁻¹ * r⁻¹, hc⟩ := by
    rw [hρr, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [he]
  have hOL : pCoreOf 2 (Lv L v) ≤ Lv L v := pCoreOf_le 2 _
  have hO2 : autOn (pCoreOf 2 (Lv L v)) U ≤ pCoreOf 2 (autOn (Lv L v) U) := by
    refine le_pCoreOf_of_le_normalizer 2 (InternalSec.autOn_le_autOn_of_le hOL)
      (autOn_le_normalizer (le_normalizer_pCoreOf 2 _)) ?_
    have hOU : pCoreOf 2 (Lv L v) ≤ Subgroup.normalizer (U : Set G) :=
      hOL.trans (hC.lv_le.trans (Kv_le_normalizer_Usec hC))
    have h1 : IsPGroup 2 ↥((pCoreOf 2 (Lv L v)).subgroupOf (Subgroup.normalizer (U : Set G))) :=
      (pCoreOf_isPGroup 2 _).of_equiv (Subgroup.subgroupOfEquivOfLe hOU).symm
    exact h1.map (conjAct U)
  exact hO2 (QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨_, hc⟩, hlr, rfl⟩)

omit [Finite G] in
theorem autOn_ne_bot {R U : Subgroup G} (hRU : R ≤ Subgroup.normalizer (U : Set G))
    (h : ¬ R ≤ Subgroup.centralizer (U : Set G)) : autOn R U ≠ ⊥ :=
  CFSG.Quasithin.AutOn.autOn_ne_bot_of_not_le_centralizer hRU h

theorem inf_normalizer_le' (h1222 : Stmt12_2_2) (hD2 : Lemma12_6_4_5) (hD7 : Lemma12_6_13)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hN : Subgroup.normalizer (Rv T L v : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    autOn Kv (Usec Kv S) ⊓ Subgroup.normalizer (autOn (Rsec L Kv S v) (Usec Kv S) :
      Set (MulAut ↥(Usec Kv S))) ≤
      Subgroup.normalizer (autOn (Lv L v) (Usec Kv S) : Set (MulAut ↥(Usec Kv S))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  obtain ⟨-, -, -, -, -, hOR, -, -, hReq⟩ := hD2 G T L V F v Kv S hC
  set U := Usec Kv S with hU
  set R := Rsec L Kv S v with hR
  have hXU : Kv ⊔ S ≤ Subgroup.normalizer (U : Set G) :=
    (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_Usec Kv S)
  have hSU : S ≤ Subgroup.normalizer (U : Set G) := (le_sup_right : S ≤ Kv ⊔ S).trans hXU
  have hRS : R ≤ S := hReq ▸ centralizerSection_le_left _ _ _
  have hRU : R ≤ Subgroup.normalizer (U : Set G) := hRS.trans hSU
  rintro a ⟨ha, haN⟩
  obtain ⟨⟨k, hkN⟩, hkK, rfl⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 ha
  have hkR : ∀ r ∈ R, k * r * k⁻¹ ∈ R := by
    intro r hr
    have h1 : conjAct U ⟨k, hkN⟩ * conjAct U ⟨r, hRU hr⟩ * (conjAct U ⟨k, hkN⟩)⁻¹ ∈
        autOn R U :=
      (Subgroup.mem_normalizer_iff.1 haN _).1
        (QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨r, hRU hr⟩, hr, rfl⟩)
    obtain ⟨⟨r', hr'N⟩, hr'R, hr'⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 h1
    have hkrN : k * r * k⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN (hRU hr)) (Subgroup.inv_mem _ hkN)
    have h2 : conjAct U (⟨r', hr'N⟩⁻¹ * ⟨k * r * k⁻¹, hkrN⟩) = 1 := by
      rw [map_mul, map_inv, hr']
      have : conjAct U ⟨k * r * k⁻¹, hkrN⟩ =
          conjAct U ⟨k, hkN⟩ * conjAct U ⟨r, hRU hr⟩ * (conjAct U ⟨k, hkN⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [this, inv_mul_cancel]
    have h3 := (QuasithinUnique.Setup.rho_eq_one_iff
      (P := Subgroup.normalizer (U : Set G)) le_rfl _).1 h2
    have h4 : r'⁻¹ * (k * r * k⁻¹) ∈ pCoreOf 2 (Kv ⊔ S) := by
      rw [hO]
      refine ⟨(Kv ⊔ S).mul_mem ((Kv ⊔ S).inv_mem ((le_sup_right : S ≤ Kv ⊔ S) (hRS hr'R)))
        ((Kv ⊔ S).mul_mem ((Kv ⊔ S).mul_mem ((le_sup_left : Kv ≤ Kv ⊔ S) hkK)
          ((le_sup_right : S ≤ Kv ⊔ S) (hRS hr))) ((Kv ⊔ S).inv_mem
            ((le_sup_left : Kv ≤ Kv ⊔ S) hkK))), h3⟩
    have h5 := hOR h4
    have e : k * r * k⁻¹ = r' * (r'⁻¹ * (k * r * k⁻¹)) := by group
    rw [e]
    exact R.mul_mem hr'R h5
  have hkNR : k ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨hkR r, fun h => ?_⟩
    have hinj : Set.InjOn (fun x => k * x * k⁻¹) (R : Set G) := fun x _ y _ hxy => by
      simpa using hxy
    have hmaps : Set.MapsTo (fun x => k * x * k⁻¹) (R : Set G) (R : Set G) :=
      fun x hx => hkR x hx
    have hsurj := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite _) hmaps).1 hinj
    obtain ⟨x, hx, hxe⟩ := hsurj.2.2 h
    have : x = r := by simpa using hxe
    rw [← this]
    exact hx
  have hkL := normalizer_Rsec_le h1222 hD2 hC hN ⟨hkK, hkNR⟩
  exact autOn_le_normalizer ((Subgroup.zpowers_le).2 hkL)
    (QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨k, hkN⟩, Subgroup.mem_zpowers k, rfl⟩)

theorem autOn_Lv_lt' (h1222 : Stmt12_2_2) (hD2 : Lemma12_6_4_5) (hD5 : Lemma12_6_11)
    (hD7 : Lemma12_6_13) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S)
    (hN : Subgroup.normalizer (Rv T L v : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    autOn (Lv L v) (Usec Kv S) < autOn Kv (Usec Kv S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM := (hD5 G T L V F v Kv S hC).2
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  obtain ⟨-, -, -, -, -, hOR, -, -, -⟩ := hD2 G T L V F v Kv S hC
  have hRR := Rsec_eq_Rv h1222 hD2 hC hN
  refine lt_of_le_of_ne (InternalSec.autOn_le_autOn_of_le hC.lv_le) fun heq => hKM ?_
  intro k hk
  have hkN : k ∈ Subgroup.normalizer (Usec Kv S : Set G) := Kv_le_normalizer_Usec hC hk
  have hkA : conjAct (Usec Kv S) ⟨k, hkN⟩ ∈ autOn (Lv L v) (Usec Kv S) := by
    rw [heq]
    exact QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨k, hkN⟩, hk, rfl⟩
  obtain ⟨⟨l, hlN⟩, hlL, hlk⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 hkA
  have hc : ((⟨l, hlN⟩⁻¹ * ⟨k, hkN⟩ : ↥(Subgroup.normalizer (Usec Kv S : Set G))) : G) ∈
      Subgroup.centralizer (Usec Kv S : Set G) := by
    rw [← QuasithinUnique.Setup.rho_eq_one_iff (P := Subgroup.normalizer (Usec Kv S : Set G))
      le_rfl]
    show conjAct (Usec Kv S) (⟨l, hlN⟩⁻¹ * ⟨k, hkN⟩) = 1
    rw [map_mul, map_inv, hlk, inv_mul_cancel]
  have hlK : l ∈ Kv := hC.lv_le hlL
  have hcO : l⁻¹ * k ∈ pCoreOf 2 (Kv ⊔ S) := by
    rw [hO]
    exact ⟨(Kv ⊔ S).mul_mem ((Kv ⊔ S).inv_mem ((le_sup_left : Kv ≤ Kv ⊔ S) hlK))
      ((le_sup_left : Kv ≤ Kv ⊔ S) hk), hc⟩
  have hcR : l⁻¹ * k ∈ Rv T L v := hRR ▸ hOR hcO
  have hcLT : l⁻¹ * k ∈ L ⊔ T := ((pCoreOf_le 2 _).trans inf_le_left) hcR
  have hLTM : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hC.hyp.hyp.normalizes
  have e : k = l * (l⁻¹ * k) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer (Lv_le_L L v hlL)) (hLTM hcLT)

end S126T2

end CFSG.Quasithin.H13
