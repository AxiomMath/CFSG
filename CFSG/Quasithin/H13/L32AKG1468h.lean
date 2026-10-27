module

public import CFSG.Quasithin.H13.L32AKG1468g
public import CFSG.Quasithin.H13.L32AKG1468c
public import CFSG.Quasithin.H13.L32AKG1468f

public noncomputable section

namespace CFSG.Quasithin.H13.KGRu

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits Matrix

theorem normalizer_quot_sl32
    {G : Type} [Group G] [Finite G] {Y : Subgroup G} (hq : CFSG.IsQuasisimple ↥Y)
    (hRu : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.Carrier .Ru))
    {z : G} (hzY : z ∈ Y) (hzC : z ∉ Subgroup.centralizer (Y : Set G))
    {E : Subgroup G} (hEO : E ≤ pCoreOf 2 (oTwoUpper (Y ⊓ Subgroup.centralizer ({z} : Set G))))
    (hEe : IsElemAbelian 2 E) (hE8 : Nat.card E = 8) (hzE : z ∈ E)
    (hEZ : E ⊓ Subgroup.centralizer (Y : Set G) = ⊥)
    (hcomm : ∀ e ∈ E, ∀ w ∈ pCoreOf 2 (oTwoUpper (Y ⊓ Subgroup.centralizer ({z} : Set G))),
      e * w * e⁻¹ * w⁻¹ ∈ Subgroup.zpowers z)
    {y : G} (hyK : y ∈ oTwoUpper (Y ⊓ Subgroup.centralizer ({z} : Set G))) (hy3 : orderOf y = 3)
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hyf : ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers z → e ∈ Subgroup.zpowers z)
    {S : Subgroup G} (hS : IsSylowTwoOf S Y) (hSN : S ≤ Subgroup.normalizer (E : Set G))
    (hSz : S ≤ Subgroup.centralizer ({z} : Set G)) :
    Nonempty (↥(oTwoUpper (Y ⊓ Subgroup.normalizer (E : Set G))) ⧸
        CFSG.pCore 2 ↥(oTwoUpper (Y ⊓ Subgroup.normalizer (E : Set G))) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ, hρs, hρk, hρS⟩ := exists_rho hRu hS
  set Zc := ρ.ker with hZc_def
  have hZc : Zc ≤ Subgroup.center ↥Y := hρk ▸ pCore_le_center_of_quasisimple hq
  have hZ2 : IsPGroup 2 Zc := hρk ▸ CFSG.pCore_isPGroup
  have hZcY : ∀ x ∈ Zc, (x : G) ∈ Subgroup.centralizer (Y : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun g hg =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp (hZc hx) ⟨g, hg⟩) :)
  have hsub2 : IsPGroup 2 Y.subtype.ker := by
    rw [Subgroup.ker_subtype]
    exact IsPGroup.of_bot
  set C0 := Y ⊓ Subgroup.centralizer ({z} : Set G) with hC0
  set K₀ := oTwoUpper C0 with hK₀
  have hK₀Y : K₀ ≤ Y := (oTwoUpper_le C0).trans inf_le_left
  have hEY : E ≤ Y := hEO.trans ((pCoreOf_le 2 K₀).trans hK₀Y)
  have hyY : y ∈ Y := hK₀Y hyK
  have hSY : S ≤ Y := hS.1
  set z' : ↥Y := ⟨z, hzY⟩ with hz'
  set y' : ↥Y := ⟨y, hyY⟩ with hy'
  set E' := E.subgroupOf Y with hE'
  set S' := S.subgroupOf Y with hS'
  set KY := oTwoUpper (Subgroup.centralizer ({z'} : Set ↥Y)) with hKY
  have hKYmap : KY.map Y.subtype = K₀ := by
    rw [hKY, ← oTwoUpper_map, map_centralizer_singleton_subtype]
  have hE'map : E'.map Y.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEY
  have hPKY : (pCoreOf 2 KY).map Y.subtype = pCoreOf 2 K₀ := by
    rw [← pCoreOf_map_eq Y.subtype hsub2 KY, hKYmap]
  have hE'O : E' ≤ pCoreOf 2 KY := by
    rw [← Subgroup.map_le_map_iff_of_injective Y.subtype_injective, hE'map, hPKY]
    exact hEO
  have hz'E : z' ∈ E' := Subgroup.mem_subgroupOf.mpr hzE
  have hE'Z : E' ⊓ Zc = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxZ⟩ := Subgroup.mem_inf.mp hx
    have h1 : (x : G) ∈ E ⊓ Subgroup.centralizer (Y : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hxE, hZcY x hxZ⟩
    rw [hEZ, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have hρinj : ∀ a ∈ E', ∀ b ∈ E', ρ a = ρ b → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ E' ⊓ Zc := Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha) hb, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]⟩
    rw [hE'Z, Subgroup.mem_bot] at h1
    calc a = a * (a⁻¹ * b) := by rw [h1, mul_one]
      _ = b := by group
  have hz2 : z ^ 2 = 1 := by
    have := hEe.2 z hzE
    exact this
  have hρz : ((ρ z' : ↥ruP) : Equiv.Perm (Fin 4060)) = ruZ := by
    refine eq_ruZ_of_comm ?_ ?_ ?_
    · rw [← map_pow, show z' ^ 2 = 1 from Subtype.ext hz2, map_one]
    · intro h1
      have hzk : z' ∈ Zc := h1
      exact hzC (hZcY z' hzk)
    · intro s hs
      rw [← hρS] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
        (hSz (Subgroup.mem_subgroupOf.mp ht)))
  have hρz' : ρ z' = ⟨ruZ, ruZ_mem⟩ := Subtype.ext hρz
  have hρK : KY.map ρ = oTwoUpper (ruC.subgroupOf ruP) := by
    rw [hKY, ← oTwoUpper_centralizer_map ρ hρs hZc hZ2 z', hρz', centralizer_ruZ_P]
  have hρO : ruJ.subgroupOf ruP ≤ (pCoreOf 2 KY).map ρ := by
    rw [← pCoreOf_map_eq ρ hZ2 KY, hρK]
    exact ruJ_le_pCoreOf_oTwoUpper
  have hSN' : ∀ t ∈ S', t ∈ Subgroup.normalizer (E' : Set ↥Y) := fun t ht => by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    rw [hE', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hSN (Subgroup.mem_subgroupOf.mp ht)) e
  have hρE : E'.map ρ = ruEP := by
    set E₀ := (E'.map ρ).map ruP.subtype with hE₀
    have hE₀J : E₀ ≤ ruS := by
      have hSE : ruS.subgroupOf ruP ≤
          Subgroup.normalizer ((E'.map ρ : Subgroup ↥ruP) : Set ↥ruP) := by
        rw [← hρS]
        rintro _ ⟨t, ht, rfl⟩
        exact Subgroup.le_normalizer_map ρ ⟨t, hSN' t ht, rfl⟩
      have hE2 : IsPGroup 2 (E'.map ρ) := by
        refine IsPGroup.map ?_ ρ
        intro x
        refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
        have := hEe.2 _ (Subgroup.mem_subgroupOf.mp x.2)
        simpa using this
      have hQ := IsPGroup.to_sup_of_normal_right' (ruSylow : Sylow 2 ↥ruP).isPGroup'
        hE2 (by rw [ruSylow_coe]; exact hSE)
      have hmax := (ruSylow : Sylow 2 ↥ruP).is_maximal' hQ le_sup_left
      rintro _ ⟨a, ha, rfl⟩
      have h1 : a ∈ (ruSylow : Subgroup ↥ruP) ⊔ E'.map ρ := Subgroup.mem_sup_right ha
      rw [hmax, ruSylow_coe] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    have hE₀c : ∀ x ∈ E₀, ∀ j ∈ ruJ, x * j * x⁻¹ * j⁻¹ ∈ Subgroup.zpowers ruZ := by
      rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩ j hj
      have hjP : j ∈ ruP := ruC_le (ruJ_leC hj)
      have hj' : (⟨j, hjP⟩ : ↥ruP) ∈ (pCoreOf 2 KY).map ρ :=
        hρO (Subgroup.mem_subgroupOf.mpr hj)
      obtain ⟨w, hw, hwj⟩ := hj'
      have hc1 : (e : G) * w * (e : G)⁻¹ * (w : G)⁻¹ ∈ Subgroup.zpowers z := by
        refine hcomm _ (Subgroup.mem_subgroupOf.mp he) _ ?_
        rw [← hPKY]
        exact ⟨w, hw, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc1
      have hk' : z' ^ k = e * w * e⁻¹ * w⁻¹ := Subtype.ext (by simpa using hk)
      have h2 := congrArg (fun u => ((ρ u : ↥ruP) : Equiv.Perm (Fin 4060))) hk'
      simp only [map_zpow, map_mul, map_inv, hρz', hwj] at h2
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [show ruZ = ((⟨ruZ, ruZ_mem⟩ : ↥ruP) : Equiv.Perm (Fin 4060)) from rfl,
        ← Subgroup.coe_zpow, h2]
      simp
    have hE₀card : Nat.card E₀ = 8 := by
      rw [hE₀, Subgroup.card_map_of_injective ruP.subtype_injective]
      have hinj : Function.Injective (ρ.comp E'.subtype) := fun a b hab =>
        Subtype.ext (hρinj _ a.2 _ b.2 hab)
      have hrange : E'.map ρ = (ρ.comp E'.subtype).range := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [hrange, ← SetLike.coe_sort_coe, MonoidHom.coe_range, Nat.card_range_of_injective hinj,
        hE',
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv, hE8]
    have hzE₀ : ruZ ∈ E₀ := ⟨⟨ruZ, ruZ_mem⟩, ⟨z', hz'E, hρz'⟩, rfl⟩
    have hSE₀ : ruS ≤ Subgroup.normalizer (E₀ : Set (Equiv.Perm (Fin 4060))) := by
      intro s hs
      have hsP : s ∈ ruP := ruS_le hs
      have hs' : (⟨s, hsP⟩ : ↥ruP) ∈ S'.map ρ := by
        rw [hρS]
        exact Subgroup.mem_subgroupOf.mpr hs
      obtain ⟨t, ht, hts⟩ := hs'
      have htN : t ∈ Subgroup.normalizer (E' : Set ↥Y) := by
        rw [Subgroup.mem_normalizer_iff]
        intro e
        rw [hE', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_normalizer_iff.mp (hSN (Subgroup.mem_subgroupOf.mp ht)) e
      have h1 := Subgroup.le_normalizer_map ρ ⟨t, htN, rfl⟩
      rw [hts] at h1
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨_, (Subgroup.mem_normalizer_iff.mp h1 a).mp ha, rfl⟩
      · rintro ⟨b, hb, hbg⟩
        have hgP : g ∈ ruP := by
          have e1 : g = s⁻¹ * (s * g * s⁻¹) * s := by group
          rw [e1, ← hbg]
          exact mul_mem (mul_mem (inv_mem hsP) b.2) hsP
        refine ⟨⟨g, hgP⟩, (Subgroup.mem_normalizer_iff.mp h1 ⟨g, hgP⟩).mpr ?_, rfl⟩
        have e2 : (⟨s, hsP⟩ : ↥ruP) * ⟨g, hgP⟩ * (⟨s, hsP⟩ : ↥ruP)⁻¹ = b := Subtype.ext hbg.symm
        rw [e2]
        exact hb
    have hE₀eq := eq_ruESub_of_le hE₀J hE₀c hE₀card hzE₀ hSE₀
    rw [ruEP, ← hE₀eq, hE₀]
    exact (Subgroup.comap_map_eq_self_of_injective ruP.subtype_injective _).symm
  set NP := Subgroup.normalizer ((ruEP : Subgroup ↥ruP) : Set ↥ruP) with hNP
  set Nt := NP.comap ρ with hNt
  have hρE' : ∀ e ∈ E', ρ e ∈ ruEP := fun e he => hρE ▸ ⟨e, he, rfl⟩
  have hNN : ∀ g ∈ Subgroup.normalizer (E' : Set ↥Y), g ∈ Nt := fun g hg => by
    show ρ g ∈ NP
    have h1 := Subgroup.le_normalizer_map ρ ⟨g, hg, rfl⟩
    rw [hρE] at h1
    exact h1
  have hNtE : Nt ≤ Subgroup.normalizer (E' : Set ↥Y) := by
    have hM : ∀ g ∈ Nt, ∀ e ∈ E', ∃ e' ∈ E', e'⁻¹ * (g * e * g⁻¹) ∈ Zc := by
      intro g hg e he
      have hge : ρ (g * e * g⁻¹) ∈ E'.map ρ := by
        rw [map_mul, map_mul, map_inv, hρE]
        exact (Subgroup.mem_normalizer_iff.mp hg (ρ e)).mp (hρE' e he)
      obtain ⟨e', he', he'g⟩ := hge
      exact ⟨e', he', by rw [MonoidHom.mem_ker, map_mul, map_inv, he'g, inv_mul_cancel]⟩
    have hSNt : S' ≤ Nt ⊓ Subgroup.normalizer (E' : Set ↥Y) := fun t ht =>
      Subgroup.mem_inf.mpr ⟨hNN t (hSN' t ht), hSN' t ht⟩
    have hodd : Odd ((Nt ⊓ Subgroup.normalizer (E' : Set ↥Y)).relIndex Nt) := by
      have h1 := Subgroup.relIndex_mul_relIndex S' (Nt ⊓ Subgroup.normalizer (E' : Set ↥Y)) Nt
        hSNt inf_le_left
      have h2 := Subgroup.relIndex_mul_index (hSNt.trans inf_le_left)
      have hS'odd : Odd S'.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hS.2.2)
      rw [← h2, ← h1] at hS'odd
      exact (Nat.odd_mul.mp (Nat.odd_mul.mp hS'odd).1).2
    have hE2 : ∀ e ∈ E', e * e = 1 := fun e he => Subtype.ext (by
      have := hEe.2 _ (Subgroup.mem_subgroupOf.mp he)
      rw [pow_two] at this
      simpa using this)
    have hEc : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := fun a ha b hb => Subtype.ext (by
      have := hEe.1.is_comm.comm ⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩
        ⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩
      simpa using congrArg Subtype.val this)
    have hsS : ruSGens.getD 0 1 ∈ ruS := ruSGens_getD_mem' 0
    have hsP := ruS_le hsS
    have hs' : (⟨_, hsP⟩ : ↥ruP) ∈ S'.map ρ := by
      rw [hρS]
      exact Subgroup.mem_subgroupOf.mpr hsS
    obtain ⟨s₀, hs₀, hs₀ρ⟩ := hs'
    have heE : ruEElt 2 ∈ ruESub := mem_ruESub.2 (Or.inr ⟨2, by norm_num, rfl⟩)
    have heP := ruESub_le_ruP heE
    have he' : (⟨_, heP⟩ : ↥ruP) ∈ E'.map ρ := by
      rw [hρE]
      exact Subgroup.mem_subgroupOf.mpr heE
    obtain ⟨e₀, he₀, he₀ρ⟩ := he'
    have hs₀N := hSN' s₀ hs₀
    have hcE : s₀ * e₀ * s₀⁻¹ * e₀⁻¹ ∈ E' :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hs₀N e₀).mp he₀) (inv_mem he₀)
    have hsz : s₀ * e₀ * s₀⁻¹ * e₀⁻¹ = z' := hρinj _ hcE _ hz'E (by
      apply Subtype.ext
      simp only [map_mul, map_inv, hs₀ρ, he₀ρ, hρz', Subgroup.coe_mul, Subgroup.coe_inv]
      exact ruCommS_eq)
    have hy'N : y' ∈ Subgroup.normalizer (E' : Set ↥Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro e
      rw [hE', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp hyN e
    have hy3' : y' ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← hy3]
      exact pow_orderOf_eq_one y)
    have hfpf' : ∀ e ∈ E', y' * e * y'⁻¹ * e⁻¹ ∈ Subgroup.zpowers z' →
        e ∈ Subgroup.zpowers z' := by
      intro e he hc
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
      have hc' : y * (e : G) * y⁻¹ * (e : G)⁻¹ ∈ Subgroup.zpowers z :=
        Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hyf _ (Subgroup.mem_subgroupOf.mp he) hc')
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, Subtype.ext (by simpa using hj)⟩
    exact le_normalizer_of_odd hZc hE2 hEc hE'Z hM hodd hz'E
      (Subgroup.mem_inf.mpr ⟨hNN s₀ hs₀N, hs₀N⟩) he₀ hsz
      (Subgroup.mem_inf.mpr ⟨hNN y' hy'N, hy'N⟩) hy3' hfpf'
  have hNt_eq : Nt = Subgroup.normalizer (E' : Set ↥Y) := le_antisymm hNtE hNN
  let φN : ↥Nt →* ↥NP := (ρ.comp Nt.subtype).codRestrict NP fun x => x.2
  let ψ : ↥Nt →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ruNE.comp φN
  have hψs : Function.Surjective ψ := by
    intro M
    obtain ⟨n, hn⟩ := ruNE_surjective M
    obtain ⟨g, hg⟩ := hρs (n : ↥ruP)
    have hgN : g ∈ Nt := by
      show ρ g ∈ NP
      rw [hg]
      exact n.2
    refine ⟨⟨g, hgN⟩, ?_⟩
    rw [← hn]
    show ruNE (φN ⟨g, hgN⟩) = ruNE n
    congr 1
    exact Subtype.ext hg
  have hψk : IsPGroup 2 ψ.ker := by
    intro x
    have hx1 : φN x ∈ ruNE.ker := x.2
    obtain ⟨a, ha⟩ := isPGroup_ker_ruNE ⟨_, hx1⟩
    have ha' : (φN x) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have h1 : ((x : ↥Nt) : ↥Y) ^ 2 ^ a ∈ Zc := by
      rw [MonoidHom.mem_ker, map_pow]
      exact congrArg Subtype.val ha'
    obtain ⟨b, hb⟩ := hZ2 ⟨_, h1⟩
    have hb' : (((x : ↥Nt) : ↥Y) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    refine ⟨a + b, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul]
    exact hb'
  set B := oTwoUpper Nt with hB
  let incl : ↥B →* ↥Nt := Subgroup.inclusion (oTwoUpper_le Nt)
  let ψB := ψ.comp incl
  have hψBs : Function.Surjective ψB := by
    have h1 : (oTwoUpper (⊤ : Subgroup ↥Nt)).map Nt.subtype = B := by
      rw [← oTwoUpper_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h2 : (oTwoUpper (⊤ : Subgroup ↥Nt)).map ψ = ⊤ := by
      rw [← oTwoUpper_map, Subgroup.map_top_of_surjective ψ hψs, oTwoUpper_top_sl32]
    intro M
    have hM : M ∈ (oTwoUpper (⊤ : Subgroup ↥Nt)).map ψ := h2 ▸ Subgroup.mem_top M
    obtain ⟨x, hx, rfl⟩ := hM
    have hxB : (x : ↥Y) ∈ B := h1 ▸ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hxB⟩, rfl⟩
  have hψBk : IsPGroup 2 ψB.ker := by
    let ι : ↥ψB.ker →* ↥ψ.ker :=
      { toFun := fun x => ⟨incl x, x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine hψk.of_injective ι fun x y hxy => ?_
    have := congrArg (fun w : ↥ψ.ker => (((w : ↥Nt) : ↥Y))) hxy
    exact Subtype.ext (Subtype.ext this)
  have := Vol2Native.A312L.Seven.slThree_isSimple
  have e1 := Vol2Native.A312L.modO2EquivOfHom Vol2Native.A312L.Seven.slThree_nonabelian ψB hψBs
    hψBk
  have hfin : oTwoUpper (Y ⊓ Subgroup.normalizer (E : Set G)) = B.map Y.subtype := by
    rw [← map_normalizer_subtype hEY, ← hE', ← hNt_eq, hB, oTwoUpper_map]
  rw [hfin]
  obtain ⟨e2⟩ := nonempty_quot_map_equiv Y.subtype hsub2 B
  exact ⟨e2.trans e1⟩

end CFSG.Quasithin.H13.KGRu
