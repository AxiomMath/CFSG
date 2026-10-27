module

public import CFSG.Quasithin.H13.A7Nat1233LinB51
public import CFSG.Quasithin.H13.A7Nat1233LinCover
public import CFSG.Quasithin.H13.A7Nat1233LinCode

public section

namespace CFSG.Quasithin.H13.A7.Lin

open CFSG.Open CFSG.Quasithin Subgroup Equiv
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def flagStab (K V : Subgroup G) (z : G) : Subgroup G where
  carrier := {g | g ∈ K ∧ g ∈ normalizer (V : Set G) ∧
    ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ zpowers z}
  one_mem' := ⟨K.one_mem, (normalizer _).one_mem, fun v _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haK, haN, ha⟩ ⟨hbK, hbN, hb⟩
    refine ⟨K.mul_mem haK hbK, (normalizer _).mul_mem haN hbN, fun v hv => ?_⟩
    have hw : b * v * b⁻¹ ∈ V := (mem_normalizer_iff.1 hbN v).1 hv
    have e : a * b * v * (a * b)⁻¹ * v⁻¹ =
        (a * (b * v * b⁻¹) * a⁻¹ * (b * v * b⁻¹)⁻¹) * (b * v * b⁻¹ * v⁻¹) := by group
    rw [e]
    exact (zpowers z).mul_mem (ha _ hw) (hb v hv)
  inv_mem' := by
    rintro a ⟨haK, haN, ha⟩
    refine ⟨K.inv_mem haK, (normalizer _).inv_mem haN, fun v hv => ?_⟩
    have hw : a⁻¹ * v * a ∈ V := by
      have := (mem_normalizer_iff.1 ((normalizer _).inv_mem haN) v).1 hv
      simpa using this
    have e : a⁻¹ * v * a⁻¹⁻¹ * v⁻¹ = (a * (a⁻¹ * v * a) * a⁻¹ * (a⁻¹ * v * a)⁻¹)⁻¹ := by group
    rw [e]
    exact (zpowers z).inv_mem (ha _ hw)

theorem mem_normalizer_flagStab {K V : Subgroup G} {z h : G}
    (hK : h ∈ normalizer (K : Set G)) (hV : h ∈ normalizer (V : Set G)) (hz : h * z = z * h) :
    h ∈ normalizer (flagStab K V z : Set G) := by
  have key : ∀ h, h ∈ normalizer (K : Set G) → h ∈ normalizer (V : Set G) → h * z = z * h →
      ∀ g ∈ flagStab K V z, h * g * h⁻¹ ∈ flagStab K V z := by
    intro h hK hV hz g ⟨hgK, hgN, hg⟩
    refine ⟨(mem_normalizer_iff.1 hK g).1 hgK, ?_, fun v hv => ?_⟩
    · exact (normalizer _).mul_mem ((normalizer _).mul_mem hV hgN) ((normalizer _).inv_mem hV)
    · have hw : h⁻¹ * v * h ∈ V := by
        have := (mem_normalizer_iff.1 ((normalizer _).inv_mem hV) v).1 hv
        simpa using this
      obtain ⟨m, hm⟩ := mem_zpowers_iff.1 (hg _ hw)
      have hzm : h * z ^ m * h⁻¹ = z ^ m := by
        have hc : Commute h z := hz
        rw [(hc.zpow_right m).eq, mul_inv_cancel_right]
      have e : h * g * h⁻¹ * v * (h * g * h⁻¹)⁻¹ * v⁻¹ =
          h * (g * (h⁻¹ * v * h) * g⁻¹ * (h⁻¹ * v * h)⁻¹) * h⁻¹ := by group
      rw [e, ← hm, hzm]
      exact zpow_mem_zpowers z m
  rw [mem_normalizer_iff]
  intro g
  refine ⟨fun hg => key h hK hV hz g hg, fun hg => ?_⟩
  have hz' : h⁻¹ * z = z * h⁻¹ := (Commute.inv_left (hz : Commute h z)).eq
  have := key h⁻¹ ((normalizer _).inv_mem hK) ((normalizer _).inv_mem hV) hz' _ hg
  simpa [mul_assoc] using this

theorem sq_centralizes_of_mem_flagStab {K V : Subgroup G} {z y : G} (hy : y ∈ flagStab K V z)
    (hyz : y * z = z * y) (hz2 : z ^ 2 = 1) : ∀ v ∈ V, y ^ 2 * v * (y ^ 2)⁻¹ = v := by
  intro v hv
  obtain ⟨-, -, hyv⟩ := hy
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 (hyv v hv)
  have h1 : y * v * y⁻¹ = z ^ m * v := by rw [hm]; group
  have hc : Commute y z := hyz
  have hzm : y * z ^ m * y⁻¹ = z ^ m := by
    rw [(hc.zpow_right m).eq, mul_inv_cancel_right]
  have hzz : z ^ m * z ^ m = 1 := by
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, hz2]
    rw [← zpow_add, ← two_mul, zpow_mul, h2, one_zpow]
  calc y ^ 2 * v * (y ^ 2)⁻¹ = y * (y * v * y⁻¹) * y⁻¹ := by rw [sq, mul_inv_rev]; group
    _ = y * (z ^ m * v) * y⁻¹ := by rw [h1]
    _ = (y * z ^ m * y⁻¹) * (y * v * y⁻¹) := by group
    _ = (z ^ m * z ^ m) * v := by rw [hzm, h1, mul_assoc]
    _ = v := by rw [hzz, one_mul]

theorem insp1233KLin_of (h1222 : Stmt12_2_2)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) (h51 : AsB51) :
    Insp1233KLin := by
  intro G _ _ T L V hyp hS z hzV hz1 hzZ hC28 K hK hlt hTK hKM hVK hO2V h4
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set W := omegaOneCenterOf (pCoreOf 2 (K ⊔ hyp.Q)) with hWdef
  have hWe : IsElemAbelian 2 W := B2F.isElemAbelian_omegaOneCenterOf _
  have : IsMulCommutative ↥W := hWe.1
  obtain ⟨hKW, hVKW, hker, hirr, hnat, h20⟩ :=
    lin_alt8 h1222 hC27 h51 hyp hS hzV hz1 hzZ hC28 hK hlt hTK hKM hVK h4 hWdef
  obtain ⟨-, hTV, -, -⟩ := facts1233Four h1222 hyp
  have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hKzV : Kv hyp z ≤ normalizer (V : Set G) := (Kv_le_L hyp z).trans hLV
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hTz : T ≤ hyp.Gv z := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC hzZ) t ht))
  have hKH : K ≤ hyp.Gv z := le_of_mem_cComp hK
  have hz2 : z ^ 2 = 1 := hC28.V_elem.2 z hzV
  have hKzK : Kv hyp z ≤ K := hlt.le
  have hVW : V ≤ W := hVKW.trans (le_normalizer_iff_commutator_le_left.mp hKW)
  set Ks := autOn K W with hKs
  set U := commV Ks with hU
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hWe.2 w w.2)
  have hVU : ∀ v (hv : v ∈ V), (⟨v, hVW hv⟩ : ↥W) ∈ U := by
    intro v hv
    have h1 : v ∈ U.map W.subtype := by
      rw [hU, NQRigid.commV_autOn_map hKW]
      exact hVKW hv
    obtain ⟨w, hw, hwv⟩ := mem_map.1 h1
    have : w = ⟨v, hVW hv⟩ := Subtype.ext hwv
    rwa [← this]
  have hzfix : (⟨z, hVW hzV⟩ : ↥W) ∈ fixV Ks := by
    intro x hx
    obtain ⟨g, hgK, rfl⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 hx
    apply Subtype.ext
    rw [QuasithinUnique.Setup.coe_conjAct_apply]
    have hgz : (g : G) * z = z * g := mem_centralizer_singleton_iff.1 (hKH hgK)
    show (g : G) * z * (g : G)⁻¹ = z
    rw [hgz, mul_inv_cancel_right]
  have hZ1 : fixV Ks ⊓ U ≠ ⊥ := by
    intro hb
    have : (⟨z, hVW hzV⟩ : ↥W) ∈ fixV Ks ⊓ U := ⟨hzfix, hVU z hzV⟩
    rw [hb, mem_bot] at this
    exact hz1 (congrArg Subtype.val this)
  obtain ⟨π, Φ, hπs, hΦ⟩ :=
    LinCover.exists_mulEquiv_coreMod_eight hW2 hnat inf_le_left hirr.2.2.1 hZ1
  have hπb : Function.Bijective π := hπs.bijective_of_nat_card_le (by
    rw [h20, card_alternatingGroup1527d 8 (by norm_num)]
    norm_num [Nat.factorial])
  set ψ := MulEquiv.ofBijective π hπb with hψ
  have hψπ : ∀ y, π (ψ.symm y) = y := fun y => ψ.apply_symm_apply y
  have hact : ∀ (k : G) (hk : k ∈ K) (w : ↥W),
      ((((InternalSec.autOnHom hKW ⟨k, hk⟩ : ↥Ks) : MulAut ↥W) w : ↥W) : G) = k * w * k⁻¹ :=
    fun k hk w => QuasithinUnique.Setup.rho_apply_coe hKW ⟨k, hk⟩ w
  have hUinv : ∀ x ∈ Ks, ∀ u ∈ U, x u ∈ U := fun x hx u hu => hirr.2.1 ⟨x, hx⟩ u hu
  have htr : ∀ (γ : ↥(alternatingGroup (Fin 8))) (u : ↥U),
      ((Φ ⟨((π γ : ↥Ks) : MulAut ↥W) u, hUinv _ (π γ).2 _ u.2⟩ : ↥(G6.coreMod 8)) :
        G6.PermMod 8) = G6.permAct 8 (γ : Perm (Fin 8)) (Φ u) := fun γ u => by
    rw [hΦ γ u]
    rfl
  set VU : Subgroup ↥U := (V.subgroupOf W).subgroupOf U with hVUdef
  have hmemVU : ∀ u : ↥U, u ∈ VU ↔ ((u : ↥W) : G) ∈ V := fun u => by
    rw [hVUdef, mem_subgroupOf, mem_subgroupOf]
  set f : ↥U →* G6.PermMod 8 := (G6.coreMod 8).subtype.comp Φ.toMonoidHom with hf
  have hfi : Function.Injective f := (G6.coreMod 8).subtype_injective.comp Φ.injective
  set S := VU.map f with hSdef
  have hmemS : ∀ s, s ∈ S ↔ ∃ u : ↥U, ((u : ↥W) : G) ∈ V ∧ (Φ u : G6.PermMod 8) = s := by
    intro s
    rw [hSdef, mem_map]
    simp only [hmemVU]
    rfl
  have hS16 : Nat.card S = 16 := by
    rw [hSdef, card_map_of_injective hfi]
    have h1 : V.subgroupOf W ≤ U := fun w hw => hVU (w : G) hw
    rw [hVUdef, Nat.card_congr (subgroupOfEquivOfLe h1).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hVW).toEquiv]
    exact hS.card
  have hSev : S ≤ G6.coreMod 8 := by
    intro s hs
    obtain ⟨u, -, rfl⟩ := (hmemS s).1 hs
    exact (Φ u).2
  set zU : ↥U := ⟨⟨z, hVW hzV⟩, hVU z hzV⟩ with hzU
  have hΦz : (Φ zU : G6.PermMod 8) = G6.allOnes 8 := by
    have hfix : ∀ σ ∈ alternatingGroup (Fin 8),
        G6.permAct 8 σ (Φ zU : G6.PermMod 8) = Φ zU := by
      intro σ hσ
      have e : (⟨((π ⟨σ, hσ⟩ : ↥Ks) : MulAut ↥W) zU, hUinv _ (π _).2 _ zU.2⟩ : ↥U) = zU :=
        Subtype.ext (hzfix _ (π ⟨σ, hσ⟩).2)
      have := htr ⟨σ, hσ⟩ zU
      rw [e] at this
      exact this.symm
    rcases LinCode.eq_one_or_allOnes_of_fix hfix with h | h
    · exfalso
      have h1 : Φ zU = 1 := Subtype.ext h
      have h2 : zU = 1 := by rw [← map_one Φ] at h1; exact Φ.injective h1
      exact hz1 (congrArg (fun u : ↥U => ((u : ↥W) : G)) h2)
    · exact h
  have hjS : G6.allOnes 8 ∈ S := (hmemS _).2 ⟨zU, hzV, hΦz⟩
  obtain ⟨Sz, hKzS, -, -, hScard, -, -⟩ := autOn_Kv_four h1222 hyp hS hzV hz1 hzZ
  have h7 : 7 ∣ Nat.card ↥(Kv hyp z) := by
    have h1 := Subgroup.card_dvd_of_surjective (InternalSec.autOnHom_surjective hKzV)
    rw [hKzS, hScard] at h1
    exact (by norm_num : 7 ∣ 168).trans h1
  obtain ⟨k₇, hk₇⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Kv hyp z)) 7 h7
  have hk₇K : (k₇ : G) ∈ K := hKzK k₇.2
  set γ₇ := ψ.symm (InternalSec.autOnHom hKW ⟨k₇, hk₇K⟩) with hγ₇
  have hγ₇o : orderOf (γ₇ : Perm (Fin 8)) = 7 := by
    rw [Subgroup.orderOf_coe, hγ₇, MulEquiv.orderOf_eq]
    have ho : orderOf (⟨k₇, hk₇K⟩ : ↥K) = 7 := by
      rw [← Subgroup.orderOf_coe, show ((⟨k₇, hk₇K⟩ : ↥K) : G) = (k₇ : G) from rfl,
        Subgroup.orderOf_coe, hk₇]
    have hd := orderOf_map_dvd (InternalSec.autOnHom hKW) ⟨k₇, hk₇K⟩
    rw [ho] at hd
    rcases (Nat.dvd_prime (by norm_num)).1 hd with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      have hkC : (k₇ : G) ∈ centralizer (W : Set G) := (InternalSec.mem_ker_autOnHom hKW _).1 h
      obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hker) ⟨k₇, hk₇K, hkC⟩
      rw [← Subgroup.orderOf_coe, show ((⟨k₇, hk₇K, hkC⟩ : ↥(K ⊓ centralizer (W : Set G))) : G) =
        (k₇ : G) from rfl, Subgroup.orderOf_coe, hk₇] at hn
      rcases n with _ | n
      · norm_num at hn
      · have : 2 ∣ 7 := by rw [hn, pow_succ]; exact dvd_mul_left 2 _
        omega
    · exact h
  have hgS : ∀ s ∈ S, G6.permAct 8 (γ₇ : Perm (Fin 8)) s ∈ S := by
    intro s hs
    obtain ⟨u, huV, rfl⟩ := (hmemS s).1 hs
    rw [← htr γ₇ u]
    refine (hmemS _).2 ⟨_, ?_, rfl⟩
    show ((((π γ₇ : ↥Ks) : MulAut ↥W) u : ↥W) : G) ∈ V
    rw [hγ₇, hψπ, hact]
    exact (mem_normalizer_iff.1 (hKzV k₇.2) _).1 huV
  obtain ⟨σ, hσA, hσS, s₀, hs₀, hσs₀⟩ :=
    LinCode.exists_translation_permMod hS16 hjS hSev hγ₇o hgS
  obtain ⟨g, hgK, hg⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 (π ⟨σ, hσA⟩).2
  have hπσ : π ⟨σ, hσA⟩ = InternalSec.autOnHom hKW ⟨g, hgK⟩ := by
    apply Subtype.ext
    rw [← hg]
    rfl
  have hkact : ∀ u : ↥U, ((((π ⟨σ, hσA⟩ : ↥Ks) : MulAut ↥W) u : ↥W) : G) =
      (g : G) * u * (g : G)⁻¹ := fun u => by rw [hπσ, hact]
  have hkV : ∀ v ∈ V, (g : G) * v * (g : G)⁻¹ ∈ V ∧
      (g : G) * v * (g : G)⁻¹ * v⁻¹ ∈ zpowers z := by
    intro v hv
    set u : ↥U := ⟨⟨v, hVW hv⟩, hVU v hv⟩ with hudef
    have hs : (Φ u : G6.PermMod 8) ∈ S := (hmemS _).2 ⟨u, hv, rfl⟩
    obtain ⟨h1, h2⟩ := hσS _ hs
    set u' : ↥U := ⟨((π ⟨σ, hσA⟩ : ↥Ks) : MulAut ↥W) u, hUinv _ (π _).2 _ u.2⟩ with hu'def
    have hu' : ((u' : ↥W) : G) = (g : G) * v * (g : G)⁻¹ := hkact u
    have hΦu' : (Φ u' : G6.PermMod 8) = G6.permAct 8 σ (Φ u) := htr ⟨σ, hσA⟩ u
    rw [← hΦu'] at h1 h2
    refine ⟨?_, ?_⟩
    · obtain ⟨u'', hu''V, hu''⟩ := (hmemS _).1 h1
      have : u'' = u' := Φ.injective (Subtype.ext hu'')
      rw [← hu', ← this]
      exact hu''V
    · rcases h2 with h | h
      · have : u' = u := Φ.injective (Subtype.ext h)
        have h3 : (g : G) * v * (g : G)⁻¹ = v := by
          rw [← hu', this]
        rw [h3, mul_inv_cancel]
        exact one_mem _
      · have h4 : (Φ u' : G6.PermMod 8) = Φ (u * zU) := by
          rw [h, map_mul, Subgroup.coe_mul, hΦz]
        have : u' = u * zU := Φ.injective (Subtype.ext h4)
        have h5 : (g : G) * v * (g : G)⁻¹ = v * z := by
          rw [← hu', this]
          rfl
        rw [h5]
        have hvz : v * z = z * v := A4.mul_comm_of_mem_omegaOneCenterOf (hVW hv) (hVW hzV)
        rw [hvz, mul_inv_cancel_right]
        exact mem_zpowers z
  have hkN : (g : G) ∈ normalizer (V : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    have hle : V.map (MulAut.conj (g : G)).toMonoidHom ≤ V := by
      rintro _ ⟨v, hv, rfl⟩
      exact (hkV v hv).1
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_map_of_injective (MulAut.conj (g : G)).injective]
  have hkY : (g : G) ∈ flagStab K V z := ⟨hgK, hkN, fun v hv => (hkV v hv).2⟩
  have hCKV : ∀ y : G, ∀ hy : y ∈ K, (∀ v ∈ V, y * v * y⁻¹ = v) →
      y ∈ centralizer (W : Set G) := by
    intro y hy hyV
    set γ := ψ.symm (InternalSec.autOnHom hKW ⟨y, hy⟩) with hγ
    have hfix : ∀ s ∈ S, G6.permAct 8 (γ : Perm (Fin 8)) s = s := by
      intro s hs
      obtain ⟨u, huV, rfl⟩ := (hmemS s).1 hs
      rw [← htr γ u]
      have e : (⟨((π γ : ↥Ks) : MulAut ↥W) u, hUinv _ (π γ).2 _ u.2⟩ : ↥U) = u := by
        apply Subtype.ext
        apply Subtype.ext
        show ((((π γ : ↥Ks) : MulAut ↥W) u : ↥W) : G) = u
        rw [hγ, hψπ, hact]
        exact hyV _ huV
      rw [e]
    have h1 : (γ : Perm (Fin 8)) = 1 := LinCode.eq_one_of_fix_permMod hS16 hjS hSev hγ₇o hgS hfix
    have h2 : γ = 1 := Subtype.ext h1
    have h3 : InternalSec.autOnHom hKW ⟨y, hy⟩ = 1 := by
      have := congrArg ψ h2
      rwa [hγ, ψ.apply_symm_apply, map_one] at this
    exact (InternalSec.mem_ker_autOnHom hKW _).1 h3
  have hY2 : IsPGroup 2 ↥(flagStab K V z) := by
    intro y
    have hyK : (y : G) ∈ K := y.2.1
    have hyz : (y : G) * z = z * y := mem_centralizer_singleton_iff.1 (hKH hyK)
    have hsq := sq_centralizes_of_mem_flagStab y.2 hyz hz2
    have hy2W : (y : G) ^ 2 ∈ K ⊓ centralizer (W : Set G) :=
      ⟨K.pow_mem hyK 2, hCKV _ (K.pow_mem hyK 2) hsq⟩
    obtain ⟨n, hn⟩ := hker ⟨_, hy2W⟩
    refine ⟨n + 1, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hn
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h1 ⊢
    rw [pow_succ', pow_mul]
    exact h1
  have hYN : Kv hyp z ⊔ T ≤ normalizer (flagStab K V z : Set G) := by
    refine sup_le (fun h hh => ?_) (fun t ht => ?_)
    · exact mem_normalizer_flagStab (le_normalizer (hKzK hh)) (hKzV hh)
        (mem_centralizer_singleton_iff.1 (Kv_le_centralizer hyp z hh))
    · exact mem_normalizer_flagStab (hTK ht) (hTV ht) (mem_centralizer_singleton_iff.1 (hTz ht))
  have hYT : flagStab K V z ≤ T := by
    have hsyl := isSylowTwoOf_of_le hyp.sylow (le_sup_right : T ≤ flagStab K V z ⊔ T)
    have hn : ((flagStab K V z).subgroupOf (flagStab K V z ⊔ T)).Normal :=
      (normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le le_normalizer (le_sup_right.trans hYN))
    exact A4.le_of_normal_of_isSylowTwoOf hsyl le_sup_left hn hY2
  have hYO : flagStab K V z ≤ pCoreOf 2 (Kv hyp z ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hYT.trans le_sup_right) hYN hY2
  have hkC := hO2V (hYO hkY)
  apply hσs₀
  obtain ⟨u₀, hu₀V, rfl⟩ := (hmemS s₀).1 hs₀
  rw [← htr ⟨σ, hσA⟩ u₀]
  have e : (⟨((π ⟨σ, hσA⟩ : ↥Ks) : MulAut ↥W) u₀, hUinv _ (π _).2 _ u₀.2⟩ : ↥U) = u₀ := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hkact]
    have := mem_centralizer_iff.1 hkC _ hu₀V
    rw [← this, mul_inv_cancel_right]
  rw [e]

end CFSG.Quasithin.H13.A7.Lin
