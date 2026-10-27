module

public import CFSG.Quasithin.Background.RonanF918FiveIii
public import CFSG.Quasithin.Background.RonanF918FiveO2

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped Pointwise commutatorElement

section Module

variable {W : Type} [CommGroup W] [Finite W]

theorem noFix_mod {Mp : Subgroup (MulAut W)} {V : Subgroup W} (hinv : XMod.IsInv ↥Mp V)
    (hirr : XMod.IsIrrSec ↥Mp (XMod.fixed ↥Mp V) V) (hperf : XMod.commOf ↥Mp V = V) {c : W}
    (hc : c ∈ V) (hcm : ∀ m ∈ Mp, m c * c⁻¹ ∈ fixV Mp) : c ∈ fixV Mp := by
  let S : Subgroup W :=
    { carrier := {c | c ∈ V ∧ ∀ m ∈ Mp, m c * c⁻¹ ∈ fixV Mp}
      one_mem' := ⟨V.one_mem, fun m _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨V.mul_mem ha.1 hb.1, fun m hm => by
        have e : m (a * b) * (a * b)⁻¹ = (m a * a⁻¹) * (m b * b⁻¹) := by
          rw [map_mul, mul_inv, mul_mul_mul_comm]
        rw [e]
        exact (fixV Mp).mul_mem (ha.2 m hm) (hb.2 m hm)⟩
      inv_mem' := fun {a} ha => ⟨V.inv_mem ha.1, fun m hm => by
        have e : m a⁻¹ * (a⁻¹)⁻¹ = (m a * a⁻¹)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv, inv_inv]
        rw [e]
        exact (fixV Mp).inv_mem (ha.2 m hm)⟩ }
  have hSV : S ≤ V := fun s hs => hs.1
  have hfixS : XMod.fixed ↥Mp V ≤ S := fun s hs => ⟨hs.1, fun m hm => by
    have : m s = s := hs.2 ⟨m, hm⟩
    rw [this]; simp⟩
  have hSinv : XMod.IsInv ↥Mp S := by
    intro a s hs
    have has : a • s ∈ V := hinv a s hs.1
    refine ⟨has, fun m hm => ?_⟩
    have hconj : (a : MulAut W)⁻¹ * m * (a : MulAut W) ∈ Mp :=
      Mp.mul_mem (Mp.mul_mem (Mp.inv_mem a.2) hm) a.2
    have h1 := hs.2 _ hconj
    have e : m (a • s) * (a • s)⁻¹ =
        (a : MulAut W) (((a : MulAut W)⁻¹ * m * (a : MulAut W)) s * s⁻¹) := by
      show m ((a : MulAut W) s) * ((a : MulAut W) s)⁻¹ = _
      simp [MulAut.mul_apply, map_mul, map_inv]
    rw [e, mem_fixV.mp h1 (a : MulAut W) a.2]
    exact h1
  have hcS : c ∈ S := ⟨hc, hcm⟩
  rcases hirr.2 S hSinv hfixS hSV with hS | hS
  · have hcf : c ∈ XMod.fixed ↥Mp V := by rw [← hS]; exact hcS
    intro m hm
    exact hcf.2 ⟨m, hm⟩
  · exfalso
    have hall : ∀ v ∈ V, ∀ m ∈ Mp, m v * v⁻¹ ∈ fixV Mp := fun v hv m hm => by
      have hvS : v ∈ S := by rw [hS]; exact hv
      exact hvS.2 m hm
    have hcomm : V ≤ fixV Mp := by
      rw [← hperf]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨a, l, hl, rfl⟩
      exact hall l hl a a.2
    have hfV : XMod.fixed ↥Mp V = V := le_antisymm (fun v hv => hv.1) fun v hv =>
      ⟨hv, fun a => (mem_fixV.mp (hcomm hv)) a a.2⟩
    exact hirr.1.ne hfV

theorem noFix_of_gen {Mp L L' : Subgroup (MulAut W)} {V : Subgroup W} (hinv : XMod.IsInv ↥Mp V)
    (hirr : XMod.IsIrrSec ↥Mp (XMod.fixed ↥Mp V) V) (hperf : XMod.commOf ↥Mp V = V)
    (hgen : ∀ m ∈ Mp, ∃ a ∈ L, ∃ b ∈ L', m = a * b) (hL' : ∀ b ∈ L', ∀ c ∈ V, b c = c) {c : W}
    (hc : c ∈ V) (hcL : ∀ a ∈ L, a c * c⁻¹ ∈ fixV Mp) : c ∈ fixV Mp := by
  refine noFix_mod hinv hirr hperf hc fun m hm => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := hgen m hm
  have : (a * b) c = a c := by rw [MulAut.mul_apply, hL' b hb c hc]
  rw [this]
  exact hcL a ha

theorem fixed_mod_le_comm_sup {Mp L L' : Subgroup (MulAut W)} {V : Subgroup W} {g : MulAut W}
    (hL'g : L' = conjAutSub g L) (hL'Mp : L' ≤ Mp)
    (hgen : ∀ m ∈ Mp, ∃ a ∈ L, ∃ b ∈ L', m = a * b) (hinv : XMod.IsInv ↥Mp V)
    (hirr : XMod.IsIrrSec ↥Mp (XMod.fixed ↥Mp V) V) (hperf : XMod.commOf ↥Mp V = V)
    (hA : commV L = V) (hinc : commV L ≤ fixV L')
    (hsum : IsSumMod (fixV Mp) (commV L) ((commV L).map g.toMonoidHom) ⊤)
    (hgF : g ∈ stabSub (fixV Mp)) {w : W} (hw : ∀ y ∈ L', y w * w⁻¹ ∈ fixV Mp) :
    w ∈ commV L ⊔ fixV Mp := by
  have hw' : w ∈ commV L ⊔ (commV L).map g.toMonoidHom ⊔ fixV Mp := by
    rw [← hsum.1]; exact Subgroup.mem_top w
  obtain ⟨ab, hab, f, hf, rfl⟩ := Subgroup.mem_sup.mp hw'
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hab
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
  have hb'V : b' ∈ V := by rw [← hA]; exact hb'
  have hL'V : ∀ y ∈ L', ∀ c ∈ V, y c = c := fun y hy c hc =>
    (mem_fixV.mp (hinc (by rw [hA]; exact hc))) y hy
  have hy : ∀ l ∈ L, l b' * b'⁻¹ ∈ fixV Mp := by
    intro l hl
    have hyL' : g * l * g⁻¹ ∈ L' := by
      rw [hL'g]
      exact ⟨l, hl, by simp [MulAut.conj_apply]⟩
    have h1 := hw _ hyL'
    have ha_fix : (g * l * g⁻¹) a = a := (mem_fixV.mp (hinc ha)) _ hyL'
    have hf_fix : (g * l * g⁻¹) f = f := (mem_fixV.mp hf) _ (hL'Mp hyL')
    have e : (g * l * g⁻¹) (a * g b' * f) * (a * g b' * f)⁻¹ = g (l b' * b'⁻¹) := by
      have hmid : (g * l * g⁻¹) (g b') = g (l b') := by simp [MulAut.mul_apply]
      rw [map_mul, map_mul, ha_fix, hf_fix, hmid, map_mul, map_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    have h1' : (g * l * g⁻¹) (a * g b' * f) * (a * g b' * f)⁻¹ ∈ fixV Mp := h1
    rw [e] at h1'
    exact (hgF (l b' * b'⁻¹)).mp h1'
  have hb'F : b' ∈ fixV Mp :=
    noFix_of_gen hinv hirr hperf hgen hL'V hb'V hy
  have hgbF : g.toMonoidHom b' ∈ fixV Mp := (hgF b').mpr hb'F
  exact (commV L ⊔ fixV Mp).mul_mem
    ((commV L ⊔ fixV Mp).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hgbF))
    (Subgroup.mem_sup_right hf)

end Module

section Hat

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem hat_eq_centralizer (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {t : G}
    (htH : t ∈ H)
    (hcen : commV (autIH V₁ I H K) ≤ fixV (autIH V₁ I H (conjSub t⁻¹ K)))
    (hmod : ∀ w : ↥(tildeOf V₁ (conjClosure I H)),
      (∀ y ∈ autIH V₁ I H (conjSub t⁻¹ K), y w * w⁻¹ ∈ fixV (autIH V₁ I H (conjClosure K T))) →
        w ∈ commV (autIH V₁ I H K) ⊔ fixV (autIH V₁ I H (conjClosure K T))) :
    hat' V₁ Vp H K T ⁅conjClosure I H, K⁆ =
      hat' V₁ Vp H K T (conjClosure I H) ⊓
        Subgroup.centralizer (hat' V₁ Vp H K T (conjSub t⁻¹ K) :
          Set (GhOf V₁ (conjClosure Vp H) (conjClosure K T))) := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hKtH : conjSub t⁻¹ K ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem (H.inv_mem htH) (hKH hx)) (H.inv_mem (H.inv_mem htH))
  have hJle : ⁅conjClosure I H, K⁆ ≤ conjClosure I H := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hKH.trans (le_normalizer_conjClosure I H))
  ext z
  constructor
  · intro hz
    refine Subgroup.mem_inf.mpr ⟨secImg_mono (secImg_mono hJle) hz, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨k, hk, rfl⟩ := (mem_hat_iff h hKtH).mp hs
    rw [hat_eq_map_theta h hIU hJle] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [← commV_autIH_eq_subM h hIU hKH] at hw
    have hact : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨k, hKtH hk⟩ ∈
        autIH V₁ I H (conjSub t⁻¹ K) := by
      rw [autIH_eq_map h hKtH]
      exact ⟨⟨k, hKtH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have h1 := thetaMap_actH h hIU (hKtH hk) w
    rw [(mem_fixV.mp (hcen hw)) _ hact] at h1
    rw [eq_mul_inv_iff_mul_eq] at h1
    exact h1.symm
  · intro hz'
    obtain ⟨hz, hzc⟩ := Subgroup.mem_inf.mp hz'
    rw [hat_eq_map_theta h hIU le_rfl, subM_self] at hz
    obtain ⟨w, -, rfl⟩ := hz
    have hmem : w ∈ commV (autIH V₁ I H K) ⊔ fixV (autIH V₁ I H (conjClosure K T)) := by
      refine hmod w fun y hy => ?_
      rw [autIH_eq_map h hKtH] at hy
      obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := hy
      have hk' : k ∈ conjSub t⁻¹ K := Subgroup.mem_subgroupOf.mp hk
      have hs := kbarOf_mem_hat_of_mem h hKtH hk'
      have h1 := (Subgroup.mem_centralizer_iff.mp hzc) _ hs
      have h2 := thetaMap_actH h hIU hkH w
      have h3 : thetaMap h hIU (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
          ⟨k, hkH⟩ w) = thetaMap h hIU w := by
        rw [h2, h1, mul_inv_cancel_right]
      refine mem_fixV_of_thetaMap_eq_one h hIU ?_
      rw [map_mul, map_inv, h3, mul_inv_cancel]
    obtain ⟨a, ha, f, hf, rfl⟩ := Subgroup.mem_sup.mp hmem
    rw [map_mul, thetaMap_eq_one_of_mem_fixV h hIU hf, mul_one, hat_eq_map_theta h hIU hJle]
    refine ⟨a, ?_, rfl⟩
    rw [← commV_autIH_eq_subM h hIU hKH]
    exact ha

theorem hat_eq_of_modFiveA (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) (hK : conjClosure K T ≠ K) (hIU : I ≤ conjClosure Vp H) {t : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) (hirr : IsIrrPlusTildeT h hIU)
    (hA : commV (autIH V₁ I H K) = subM V₁ (conjClosure I H) I)
    (hsum : IsSumMod (fixV (autIH V₁ I H (conjClosure K T))) (commV (autIH V₁ I H K))
      ((commV (autIH V₁ I H K)).map
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
          ⟨t⁻¹, h.T_le_H (T.inv_mem ht)⟩).toMonoidHom) ⊤)
    (hcen : commV (autIH V₁ I H K) ≤ fixV (conjAutSub
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, h.T_le_H (T.inv_mem ht)⟩)
      (autIH V₁ I H K))) :
    hat' V₁ Vp H K T ⁅conjClosure I H, K⁆ =
      hat' V₁ Vp H K T (conjClosure I H) ⊓
        Subgroup.centralizer (hat' V₁ Vp H K T (conjSub t⁻¹ K) :
          Set (GhOf V₁ (conjClosure Vp H) (conjClosure K T))) := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have htH : t ∈ H := h.T_le_H ht
  have htiH : t⁻¹ ∈ H := H.inv_mem htH
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  obtain ⟨-, hdata⟩ := five_group_data h hH hA37 hA38 hK
  have htiK : t⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun hh => htK ((Subgroup.inv_mem_iff _).mp hh)
  obtain ⟨hKt, hK₀, hcomm, -⟩ := hdata t⁻¹ (T.inv_mem ht) htiK
  have hKtH : conjSub t⁻¹ K ≤ H := le_of_mem_cComp hKt
  have hPH : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hL'g : autIH V₁ I H (conjSub t⁻¹ K) =
      conjAutSub (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, htiH⟩)
        (autIH V₁ I H K) := (conjAutSub_autIH h hKH htiH).symm
  have hL'Mp : autIH V₁ I H (conjSub t⁻¹ K) ≤ autIH V₁ I H (conjClosure K T) :=
    CFSG.Quasithin.AutOn.autOn_mono (secImg_mono (hK₀ ▸ le_sup_right))
  have hgen : ∀ m ∈ autIH V₁ I H (conjClosure K T), ∃ a ∈ autIH V₁ I H K,
      ∃ b ∈ autIH V₁ I H (conjSub t⁻¹ K), m = a * b := by
    intro m hm
    rw [autIH_eq_map h h.K₀_le_H] at hm
    obtain ⟨⟨x, hxH⟩, hx, rfl⟩ := hm
    have hxK₀ : x ∈ conjClosure K T := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨a, ha, b, hb, p, hp, hxe⟩ := exists_mul_of_mem_sup (hKH.trans hPH) (hKtH.trans hPH) hcomm
      x (hK₀ ▸ hxK₀)
    have haH : a ∈ H := hKH ha
    have hbH : b ∈ H := hKtH hb
    have hpH : p ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hp
    refine ⟨actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨a, haH⟩, ?_,
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨b, hbH⟩, ?_, ?_⟩
    · rw [autIH_eq_map h hKH]
      exact ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    · rw [autIH_eq_map h hKtH]
      exact ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    · have hp1 := h.actH_eq_one_of_mem_pCoreOf hIU (x := ⟨p, hpH⟩) hp
      have e : (⟨x, hxH⟩ : ↥H) = ⟨a, haH⟩ * ⟨b, hbH⟩ * ⟨p, hpH⟩ := Subtype.ext hxe
      rw [e, map_mul, map_mul, hp1, mul_one]
  have hgN : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, htiH⟩ ∈
      Subgroup.normalizer (autIH V₁ I H (conjClosure K T) : Set
        (MulAut ↥(tildeOf V₁ (conjClosure I H)))) := by
    have hc : conjAutSub (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, htiH⟩)
        (autIH V₁ I H (conjClosure K T)) = autIH V₁ I H (conjClosure K T) := by
      rw [conjAutSub_autIH h h.K₀_le_H htiH]
      congr 1
      exact A38.map_conj_eq_iff.mpr (h.K₀_normal htiH)
    exact A38.map_conj_eq_iff.mp hc
  have hgF : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, htiH⟩ ∈
      stabSub (fixV (autIH V₁ I H (conjClosure K T))) :=
    FixVLat.le_stabSub_fixV_of_le_normalizer (X := Subgroup.zpowers _)
      (Subgroup.zpowers_le.mpr hgN) (Subgroup.mem_zpowers _)
  have hcen' : commV (autIH V₁ I H K) ≤ fixV (autIH V₁ I H (conjSub t⁻¹ K)) := by
    rw [hL'g]; exact hcen
  exact hat_eq_centralizer h hIU htH hcen' fun w hw =>
    fixed_mod_le_comm_sup hL'g hL'Mp hgen hirr'.1.2.1 hirr'.1.2.2.2 hirr'.1.2.2.1 hA hcen' hsum hgF hw

end Hat

end CFSG.Quasithin.RonanF918
