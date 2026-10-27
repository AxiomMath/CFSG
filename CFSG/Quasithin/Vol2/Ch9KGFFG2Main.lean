module

public import CFSG.Quasithin.Vol2.Ch9KGFFG2Nat
public import CFSG.Quasithin.Vol2.Ch9KGFFSpMain
public import CFSG.Quasithin.Vol2.Ch9KGFFMain

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.QuasithinUnique.Setup.X6
open scoped IsMulCommutative

section Parab

variable {G : Type} [Group G] [Finite G]

theorem exists_parab_of_not_alt7
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts) (h56 : AsB56)
    {Y T K KY U : Subgroup G} (hSQ : SQTKGroup ↥Y) (hT : IsSylowTwoOf T Y) (hKY : K ≤ Y)
    (hKl : K ∈ lFamily T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hA5 : Nonempty (O2Q K ≃* alternatingGroup (Fin 5))) (hKYc : KY ∈ cComp Y) (hlt : K < KY)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y U)
    (hJ : ¬ ⁅KY, thompsonJ T⁆ ≤ Subgroup.centralizer (U : Set G))
    (hnK : ¬ KY ≤ K ⊔ (KY ⊓ Subgroup.centralizer (U : Set G)))
    (hKU : ¬ K ≤ Subgroup.centralizer (U : Set G)) (hX : ¬ IsAlt 7 ↥(autOn KY U)) :
    ∃ P, IsMaxParabolic2 (modO2Image Y KY) P ∧ modO2Image Y K = perfectCore P := by
  have : IsMulCommutative ↥U := hred.2.2.1.1
  have hqbar := isQuasisimple_modO2Image h36 h312 h314 h56 hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY
    hred hJ hnK hKU
  obtain ⟨hlt', h314bar⟩ := FFB.a314_bar h36 h312 h314 hSQ hT hKY hKl hTK hA5 hKYc hlt
  obtain ⟨e⟩ := FFB.nonempty_o2q_equiv hSQ hKYc hYKY
  have hqKY : CFSG.IsQuasisimple (O2Q KY) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqbar
  obtain ⟨hqA, hlist, h60, π, hπ⟩ := autOn_facts' h56 hSQ hT hlt.le hKYc hYKY hred
    (perfect_of_mem_cComp hKl) hA5 hJ hKU hqKY
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hqKY
  set π' : ↥(modO2Image Y KY) →* ↥(autOn KY U) := π.comp e.symm.toMonoidHom with hπ'
  have hπ's : Function.Surjective π' := hπ.comp e.symm.surjective
  have hne : π'.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple hqA
    obtain ⟨x, rfl⟩ := hπ's a
    obtain ⟨y, rfl⟩ := hπ's b
    have hx : x ∈ π'.ker := by rw [htop]; exact Subgroup.mem_top x
    have hy : y ∈ π'.ker := by rw [htop]; exact Subgroup.mem_top y
    rw [MonoidHom.mem_ker] at hx hy
    rw [hx, hy] at hab
    exact hab rfl
  have hker : π'.ker ≤ Subgroup.center ↥(modO2Image Y KY) :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hqbar inferInstance).resolve_left hne
  have hc : FFB.CmpHyp (modO2Image Y KY) ↥(autOn KY U) :=
    { quasi := hqbar
      center_odd := by
        rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
        exact hodd
      map := ⟨π', hπ's, hker, hne⟩
      list := hlist
      quasiX := hqA
      dvd60 := h60 }
  exact cmp_parab h314 hc h314bar hlt' hX

omit [Finite G] in
theorem psi_injective_of_center {Y K KY U : Subgroup G} (hKYc : KY ∈ cComp Y) (hlt : K < KY)
    (hred : IsTwoReducedIn Y U) (hKU : ¬ K ≤ Subgroup.centralizer (U : Set G))
    (hq : CFSG.IsQuasisimple ↥(modO2Image Y KY))
    (hZ : Subgroup.center ↥(modO2Image Y KY) = ⊥) :
    Function.Injective (psi (le_of_mem_cComp hKYc) hred) := by
  have hKYY : KY ≤ Y := le_of_mem_cComp hKYc
  have hKYN : KY ≤ Subgroup.normalizer (U : Set G) := hKYY.trans hred.2.1
  set ψ := psi hKYY hred with hψ
  have hψne : ψ.ker ≠ ⊤ := by
    intro htop
    apply hKU
    intro k hk
    have h1 : barMap hKYY ⟨k, hlt.le hk⟩ ∈ ψ.ker := by rw [htop]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hψ, psi_barMap] at h1
    exact (InternalSec.mem_ker_autOnHom hKYN ⟨k, hlt.le hk⟩).1 h1
  have hk : ψ.ker ≤ Subgroup.center ↥(modO2Image Y KY) :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hq inferInstance).resolve_left hψne
  rw [hZ, le_bot_iff] at hk
  exact (MonoidHom.ker_eq_bot_iff ψ).mp hk

theorem exists_conj_of_parab_gen {Y K KY U : Subgroup G} (hKYc : KY ∈ cComp Y) (hlt : K < KY)
    (hred : IsTwoReducedIn Y U) (hKU : ¬ K ≤ Subgroup.centralizer (U : Set G))
    (hψi : Function.Injective (psi (le_of_mem_cComp hKYc) hred))
    {S : Type} [Group S] [Finite S] {U' : Subgroup S} (hU' : IsSylowTwoOf U' ⊤)
    {P' : Fin 2 → Subgroup S} (hres : ResidualOvergroupsAt S U' P')
    (θ : S ≃* ↥(autOn KY U)) {P : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)}
    (hP : IsMaxParabolic2 (modO2Image Y KY) P) (hKP : modO2Image Y K = perfectCore P) :
    ∃ (g : S) (j : Fin 2), (autOn K U).subgroupOf (autOn KY U) =
      ((perfectCore (P' j)).map (MulAut.conj g).toMonoidHom).map θ.toMonoidHom := by
  have hKYY : KY ≤ Y := le_of_mem_cComp hKYc
  have hKYN : KY ≤ Subgroup.normalizer (U : Set G) := hKYY.trans hred.2.1
  set ψe : ↥(modO2Image Y KY) ≃* ↥(autOn KY U) := MulEquiv.ofBijective (psi hKYY hred)
    ⟨hψi, psi_surjective hKYY hred⟩ with hψe
  have hPL : P ≤ modO2Image Y KY := hP.1.1
  set P'' : Subgroup ↥(modO2Image Y KY) := P.subgroupOf (modO2Image Y KY) with hP''
  have hP''map : P''.map (modO2Image Y KY).subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  have hpar' : IsParabolic2 (⊤ : Subgroup ↥(modO2Image Y KY)) P'' := by
    rw [A312.isParabolic2_top_iff, hP''map]
    exact hP.1
  have hne' : P'' ≠ ⊤ := by
    intro htop
    apply hP.2.1
    rw [← hP''map, htop, Subgroup.map_top, Subgroup.range_subtype]
  set Pa : Subgroup S := (P''.map ψe.toMonoidHom).map θ.symm.toMonoidHom with hPa
  have hparPa : IsParabolic2 (⊤ : Subgroup S) Pa :=
    CFSG.QuasithinUnique.Vol2Native.A312L.isParabolic2_top_map_equiv θ.symm
      (CFSG.QuasithinUnique.Vol2Native.A312L.isParabolic2_top_map_equiv ψe hpar')
  have hnePa : Pa ≠ ⊤ :=
    A5.G3.map_ne_top_of_equiv θ.symm (A5.G3.map_ne_top_of_equiv ψe hne')
  have hcore : (perfectCore Pa).map θ.toMonoidHom = (autOn K U).subgroupOf (autOn KY U) := by
    rw [hPa, ← map_perfectCore, ← map_perfectCore, Subgroup.map_map]
    have hid : θ.toMonoidHom.comp θ.symm.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [hid, Subgroup.map_id, hP'', perfectCore_subgroupOf_of_le hPL, ← hKP]
    exact map_psi_modO2Image hKYY hlt.le hred
  rcases perfectCore_parabolic_conj hU' hres hparPa hnePa with hbot | ⟨g, j, hgj⟩
  · exfalso
    apply hKU
    intro k hk
    have h1 : (InternalSec.autOnHom hKYN ⟨k, hlt.le hk⟩ : ↥(autOn KY U)) ∈
        (autOn K U).subgroupOf (autOn KY U) := by
      rw [Subgroup.mem_subgroupOf]
      exact Setup.mem_autOn_iff.mpr ⟨⟨k, hKYN (hlt.le hk)⟩, hk, rfl⟩
    rw [← hcore, hbot, Subgroup.map_bot, Subgroup.mem_bot] at h1
    exact (InternalSec.mem_ker_autOnHom hKYN ⟨k, hlt.le hk⟩).1 h1
  · exact ⟨g, j, by rw [← hcore, hgj]⟩

end Parab

section Coord

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {Z : Subgroup V} {F : Type}
  [Field F] [CharP F 2]

theorem fixed_iff_of_realizes_g2 {π : ↥(CFSG.Open.quasithinG2 F) →* ↥L}
    (hR : (FFModel.zornQ (CFSG.Open.quasithinG2 F)).RealizesVia L (commV L) Z π) {x : V}
    (hx : x ∈ commV L) :
    ∃ w : Ix3 → F, ∀ γ : ↥(CFSG.Open.quasithinG2 F),
      (((π γ : ↥L) : MulAut V) x * x⁻¹ ∈ Z ↔
        Vol2.KGNat.zornLin (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) w = w) := by
  have hΓ : CFSG.Open.quasithinG2 F ≤ cayleyGroup F :=
    (CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup).le
  obtain ⟨f, hfadd, hfker, -, hfeq⟩ := Vol2.KGNat.exists_coord
    (Vol2.KGNat.linModelZorn (CFSG.Open.quasithinG2 F) hΓ) hR
  refine ⟨f x, fun γ => ?_⟩
  have hγx : ((π γ : ↥L) : MulAut V) x ∈ commV L := hR.2.2.2.1 (π γ) x hx
  have hxi : x⁻¹ ∈ commV L := (commV L).inv_mem hx
  have h1 : f (((π γ : ↥L) : MulAut V) x) =
      Vol2.KGNat.zornLin (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) (f x) := hfeq γ x hx
  have h0 : f x + f x⁻¹ = 0 := by
    rw [← hfadd x hx x⁻¹ hxi, mul_inv_cancel]
    exact (hfker 1 (commV L).one_mem).mpr Z.one_mem
  have hfi : f x⁻¹ = -f x := eq_neg_of_add_eq_zero_right h0
  rw [← hfker _ ((commV L).mul_mem hγx hxi), hfadd _ hγx _ hxi, h1, hfi, ← sub_eq_add_neg,
    sub_eq_zero]

end Coord

section Main

variable {G : Type} [Group G] [Finite G]

theorem g2Act_conj_fixed_iff {F : Type} [Field F] [CharP F 2] {S : Type} [Group S]
    (ψ : S ≃* ↥(cayleyGroup F)) (g s : S) (w : Ix3 → F) :
    g2Act (ψ (g * s * g⁻¹)) w = w ↔
      g2Act (ψ s) (g2Act (ψ g⁻¹) w) = g2Act (ψ g⁻¹) w := by
  have hid : ∀ y, g2Act (ψ g⁻¹) (g2Act (ψ g) y) = y := fun y => by
    rw [← g2Act_mul_apply', ← MulEquiv.map_mul ψ, inv_mul_cancel, MulEquiv.map_one ψ, map_one]
    rfl
  have hid' : ∀ y, g2Act (ψ g) (g2Act (ψ g⁻¹) y) = y := fun y => by
    rw [← g2Act_mul_apply', ← MulEquiv.map_mul ψ, mul_inv_cancel, MulEquiv.map_one ψ, map_one]
    rfl
  rw [MulEquiv.map_mul ψ, MulEquiv.map_mul ψ, g2Act_mul_apply', g2Act_mul_apply']
  constructor
  · intro h
    have h1 := congrArg (g2Act (ψ g⁻¹)) h
    rwa [hid] at h1
  · intro h
    rw [h, hid']

theorem false_of_g24
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts) (h51 : AsB51) (h56 : AsB56)
    {Y T K KY U U₀ : Subgroup G} {v : G} (hSQ : SQTKGroup ↥Y) (hT : IsSylowTwoOf T Y)
    (hKY : K ≤ Y) (hKl : K ∈ lFamily T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hA5 : Nonempty (O2Q K ≃* alternatingGroup (Fin 5))) (hKYc : KY ∈ cComp Y) (hlt : K < KY)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y U)
    (hJ : ¬ ⁅KY, thompsonJ T⁆ ≤ Subgroup.centralizer (U : Set G))
    (hnK : ¬ KY ≤ K ⊔ (KY ⊓ Subgroup.centralizer (U : Set G))) (hG2 : IsG2 2 2 (O2Q KY))
    (hU₀ : U₀ ≤ U) (hU₀K : U₀ ≤ ⁅U₀, K⁆) (hO2K : pCoreOf 2 K ≤ Subgroup.centralizer (U₀ : Set G))
    (hv : v ∈ U₀) (hv1 : v ≠ 1) (hKYv : KY ≤ Subgroup.centralizer ({v} : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative ↥U := hred.2.2.1.1
  have hKYY : KY ≤ Y := le_of_mem_cComp hKYc
  have hKYN : KY ≤ Subgroup.normalizer (U : Set G) := hKYY.trans hred.2.1
  have hKN : K ≤ Subgroup.normalizer (U : Set G) := hlt.le.trans hKYN
  have hKU : ¬ K ≤ Subgroup.centralizer (U : Set G) := by
    intro hKC
    have h0 : ⁅U₀, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_centralizer_iff.mp (hKC hk) u (hU₀ hu)).symm
    have := hU₀K hv
    rw [h0, Subgroup.mem_bot] at this
    exact hv1 this
  obtain ⟨hqKY, hqA, -, -, -, -⟩ :=
    kyStar_cases h36 h312 h314 h56 hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY hred hJ hnK hKU
  obtain ⟨hC, hcard, -⟩ := g24_facts hKYc hYKY hred hqKY hqA hG2
  rcases isIntDirect_or_natural_of_g24 h51 h56 hSQ hT hKYc hYKY hred hJ hqKY hqA hG2 with
    hdir | ⟨F, _, _, hF, πn, hR⟩
  · exact false_of_isIntDirect hKYN hlt.le hdir hU₀ hU₀K hv hv1 hKYv
  have : CharP F 2 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hF2 : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  have hFk : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨2, hF2⟩
  have hK4 : ∃ s : Finset F, s.card = 4 :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (le_of_eq hF.symm)
  have hU3 : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have : Nontrivial Fˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, hU3]
    norm_num
  obtain ⟨ω, hω1⟩ := exists_ne (1 : Fˣ)
  have hω : (ω : F) ≠ 1 := fun h => hω1 (Units.ext h)
  have hω3 : ω ^ 3 = 1 := by
    rw [← hU3]
    exact pow_card_eq_one'
  set θ : ↥(CFSG.Open.quasithinG2 F) ≃* ↥(autOn KY U) := MulEquiv.ofBijective πn
    ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hR, hR.1⟩ with hθ
  obtain ⟨ψ, hψ⟩ := G2M.exists_psiEquiv (F := F) hF2 (le_refl 2)
  set e₀ : ↥(cayleyGroup F) ≃* ↥(CFSG.Open.quasithinG2 F) := MulEquiv.subgroupCongr
    CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup.symm with he₀
  set Θ : ↥(adjointGroup .G2 F) ≃* ↥(autOn KY U) := ψ.trans (e₀.trans θ) with hΘ
  have hX : ¬ IsAlt 7 ↥(autOn KY U) := by
    rintro ⟨e7⟩
    have h7 := Nat.card_congr e7.toEquiv
    rw [hcard, card_alternatingGroup1527d 7 (by norm_num)] at h7
    exact absurd h7 (by decide)
  obtain ⟨P, hP, hKP⟩ := exists_parab_of_not_alt7 h36 h312 h314 h56 hSQ hT hKY hKl hTK hA5 hKYc
    hlt hYKY hred hJ hnK hKU hX
  have hqbar := isQuasisimple_modO2Image h36 h312 h314 h56 hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY
    hred hJ hnK hKU
  have hZ : Subgroup.center ↥(modO2Image Y KY) = ⊥ := by
    obtain ⟨e⟩ := FFB.nonempty_o2q_equiv hSQ hKYc hYKY
    obtain ⟨-, F', _, _, _, -, ⟨e3⟩⟩ := exists_mulEquiv_G2_model hG2
    have h1 := Subgroup.map_center_eq (e.symm.trans e3)
    rw [center_adjointGroup_eq_bot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (e.symm.trans e3).injective).mp h1
  have hψi := psi_injective_of_center hKYc hlt hred hKU hqbar hZ
  have hU₀' : IsSylowTwoOf ((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F)) ⊤ :=
    Setup.X6.isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := F) 2).1)
  obtain ⟨g, j, hgj⟩ := exists_conj_of_parab_gen hKYc hlt hred hKU hψi hU₀'
    (G2_residualOvergroupsAt (K := F)) Θ hP hKP
  set i := g2Index j with hi
  have hcore_i : perfectCore ((parabolicSubgroup Tag.G2 F {g2Index j}).subgroupOf
      (adjointGroup Tag.G2 F)) = G2M.core (F := F) i := rfl
  set Φ : ↥(adjointGroup .G2 F) →* MulAut ↥U :=
    (autOn KY U).subtype.comp (Θ.toMonoidHom.comp (MulAut.conj g).toMonoidHom) with hΦ
  have hΦL : ∀ s, Φ s ∈ autOn KY U := fun s => (Θ _).2
  have hΦπ : ∀ s, Φ s = ((πn (e₀ (ψ (g * s * g⁻¹))) : ↥(autOn KY U)) : MulAut ↥U) :=
    fun s => rfl
  have hKstar : autOn K U = (G2M.core i).map Φ := by
    have h1 := congrArg (Subgroup.map (autOn KY U).subtype) hgj
    rw [Subgroup.map_subgroupOf_eq_of_le (InternalSec.autOn_le_autOn_of_le hlt.le)] at h1
    rw [h1, Subgroup.map_map, Subgroup.map_map, hcore_i]
    rfl
  set Q : Subgroup (MulAut ↥U) := (G2M.rad i).map Φ with hQ
  set h : MulAut ↥U := Φ (G2M.hEl ω i) with hh
  have hQK : Q ≤ autOn K U := by
    rw [hKstar]
    exact Subgroup.map_mono (G2M.rad_le_core i)
  have hQO : Q ≤ pCoreOf 2 (autOn K U) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 hQK ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).map Φ)
    rw [Subgroup.normal_subgroupOf_iff hQK]
    intro q k hq hk
    rw [hKstar] at hk
    obtain ⟨n, hn, rfl⟩ := hk
    obtain ⟨r, hr, rfl⟩ := hq
    exact ⟨n * r * n⁻¹, (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hn) r).mp hr,
      by simp only [map_mul, map_inv]⟩
  have hO2 := pCoreOf_autOn_le hKN (hC.to_le (inf_le_inf_right _ hlt.le))
  have hU₀Q : ∀ q ∈ Q, ∀ u ∈ U₀.subgroupOf U, q u = u := by
    intro q hq u hu
    obtain ⟨k, hk, hkq⟩ := Setup.mem_autOn_iff.mp (hO2 (hQO hq))
    rw [← hkq]
    apply Subtype.ext
    rw [Setup.coe_conjAct_apply]
    have hku := Subgroup.mem_centralizer_iff.mp (hO2K hk) u hu
    rw [← hku, mul_inv_cancel_right]
  have hV : ∀ x : ↥U, x ^ 2 = 1 := fun x =>
    Subtype.ext (by simpa [sq] using hred.2.2.1.2 x x.2)
  have hKL : autOn K U ≤ autOn KY U := InternalSec.autOn_le_autOn_of_le hlt.le
  have h3 : h ^ 3 = 1 := by rw [hh, ← map_pow, G2M.hEl_pow_three ψ hψ hω3, map_one]
  have hconj1 : ∀ r ∈ G2M.rad (F := F) i, G2M.hEl ω i * r * (G2M.hEl ω i)⁻¹ ∈ G2M.rad i := by
    intro r hr
    have h1 := (G2M.rad i).mul_mem
      (G2M.comm_hEl_mem_rad hFk ψ hψ ω i (G2M.rad_le_core i hr)) hr
    rwa [inv_mul_cancel_right] at h1
  have hhQ : h ∈ Subgroup.normalizer (Q : Set (MulAut ↥U)) := by
    refine map_mem_normalizer_map Φ hconj1 (fun r hr => ?_)
    have hinv : (G2M.hEl ω i)⁻¹ = G2M.hEl ω i * G2M.hEl ω i := by
      rw [inv_eq_iff_mul_eq_one, ← pow_three, G2M.hEl_pow_three ψ hψ hω3]
    have h2 := hconj1 _ (hconj1 r hr)
    have e : G2M.hEl ω i * (G2M.hEl ω i * r * (G2M.hEl ω i)⁻¹) * (G2M.hEl ω i)⁻¹ =
        (G2M.hEl ω i * G2M.hEl ω i) * r * (G2M.hEl ω i * G2M.hEl ω i)⁻¹ := by
      group
    rw [e, ← hinv, inv_inv] at h2
    exact h2
  have hKQ : autOn K U ≤ Subgroup.normalizer (Q : Set (MulAut ↥U)) := by
    rw [hKstar]
    rintro _ ⟨n, hn, rfl⟩
    refine map_mem_normalizer_map Φ (fun r hr => (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hn) r).mp hr) (fun r hr => ?_)
    have := (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
      ((G2M.core i).inv_mem hn)) r).mp hr
    rwa [inv_inv] at this
  have hhK : ∀ k ∈ autOn K U, h * k * h⁻¹ * k⁻¹ ∈ Q := by
    rw [hKstar]
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨_, G2M.comm_hEl_mem_rad hFk ψ hψ ω i hn, by simp only [hh, map_mul, map_inv]⟩
  have hKP : ∀ x ∈ commV (autOn KY U), (∀ q ∈ Q, q x = x) → h x = x →
      ∀ k ∈ autOn K U, k x * x⁻¹ ∈ fixV (autOn KY U) := by
    intro x hx hxQ hxh k hk
    obtain ⟨w, hw⟩ := fixed_iff_of_realizes_g2 hR hx
    have hfix : ∀ s, Φ s x = x → g2Act (ψ s) (g2Act (ψ g⁻¹) w) = g2Act (ψ g⁻¹) w := by
      intro s hs
      refine (g2Act_conj_fixed_iff ψ g s w).mp ((hw (e₀ (ψ (g * s * g⁻¹)))).mp ?_)
      rw [← hΦπ, hs, mul_inv_cancel]
      exact Subgroup.one_mem _
    rw [hKstar] at hk
    obtain ⟨n, hn, rfl⟩ := hk
    have hn' := G2M.fixed_of_rad hFk hK4 ψ hψ hω i
      (fun r hr => hfix r (hxQ _ ⟨r, hr, rfl⟩)) (hfix _ hxh) hn
    have h1 := (hw (e₀ (ψ (g * n * g⁻¹)))).mpr ((g2Act_conj_fixed_iff ψ g n w).mpr hn')
    rw [← hΦπ] at h1
    exact h1.1
  have hU₀K' : U₀.subgroupOf U ≤ modCommOf (autOn K U) (U₀.subgroupOf U) := by
    intro u hu
    obtain ⟨y, hy, hyu⟩ := commutator_le_map_modCommOf hU₀ hKN (hU₀K hu)
    rwa [Subtype.ext hyu] at hy
  have hbot := inf_fixV_eq_bot_of_split hV hKL (hΦL _) h3 hhQ hKQ hhK hKP hU₀K' hU₀Q
  have hvU : v ∈ U := hU₀ hv
  have h2' : (⟨v, hvU⟩ : ↥U) ∈ fixV (autOn KY U) := by
    rw [FFD.fixV_autOn_eq hKYN, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hKYv hk) v rfl).symm
  have h2 : (⟨v, hvU⟩ : ↥U) ∈ U₀.subgroupOf U ⊓ fixV (autOn KY U) := ⟨hv, h2'⟩
  rw [hbot, Subgroup.mem_bot] at h2
  exact hv1 (congrArg Subtype.val h2)

end Main

end CFSG.Quasithin.H13.Ch9.KGFF

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem a314FFCohomParabFact_holds
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts) (h51 : AsB51) (h56 : AsB56) :
    A314FFCohomParabFact := by
  intro G _ _ Y T K KY U U₀ v hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY hred hJ hnK hcase hU₀ hU₀K
    hO2K hv hv1 hKYv
  rcases hcase with hSp | hG2
  · exact KGFF.false_of_sp44 h36 h312 h314 h51 h56 hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY hred hJ
      hnK hSp hU₀ hU₀K hO2K hv hv1 hKYv
  · exact KGFF.false_of_g24 h36 h312 h314 h51 h56 hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY hred hJ
      hnK hG2 hU₀ hU₀K hO2K hv hv1 hKYv

theorem a314FFCohomFact_holds
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts) (h51 : AsB51) (h56 : AsB56) :
    A314FFCohomFact :=
  a314FFCohomFact_of h36 h312 h314 h51 h56 (a314FFCohomParabFact_holds h36 h312 h314 h51 h56)

end CFSG.Quasithin.H13.Ch9
