module

public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.Quasithin.Background.F918N0
public import CFSG.Quasithin.Background.F918L1
public import CFSG.Quasithin.Background.B69Red
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LieType.Universal.Symplectic
public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Transport

theorem n4_realizesVia_transport {V₁ Y : Type} [CommGroup V₁] [CommGroup Y] {D : FFModel}
    {H : Subgroup (MulAut V₁)} {H' : Subgroup (MulAut Y)} {U Z : Subgroup V₁} {Z' : Subgroup Y}
    {π : D.Gam →* ↥H'} (e : ↥H' →* ↥H) (he : Function.Surjective e) (hZU : Z ≤ U)
    (hU : ∀ h : ↥H, ∀ u ∈ U, (h : MulAut V₁) u ∈ U) (hZ : ∀ h : ↥H, ∀ z ∈ Z, (h : MulAut V₁) z ∈ Z)
    (q : ↥U →* Y) (hq : Function.Surjective q) (hqk : ∀ u : ↥U, q u ∈ Z' ↔ (u : V₁) ∈ Z)
    (heq : ∀ (h' : ↥H') (u : ↥U) (hu : ((e h' : ↥H) : MulAut V₁) (u : V₁) ∈ U),
      q ⟨((e h' : ↥H) : MulAut V₁) (u : V₁), hu⟩ = (h' : MulAut Y) (q u))
    (h : D.RealizesVia H' ⊤ Z' π) : D.RealizesVia H U Z (e.comp π) := by
  obtain ⟨hsurj, -, hkerle, -, -, hsec, hkerinv, β', hβs, hβk, hβe⟩ := h
  let q' : ↥U →* ↥(⊤ : Subgroup Y) := (Subgroup.topEquiv (G := Y)).symm.toMonoidHom.comp q
  have hq' : Function.Surjective q' := fun y => by
    obtain ⟨u, hu⟩ := hq (y : Y)
    exact ⟨u, Subtype.ext hu⟩
  refine ⟨he.comp hsurj, hZU, hkerle, hU, hZ, hsec, hkerinv, β'.comp q', hβs.comp hq', ?_, ?_⟩
  · intro u
    rw [MonoidHom.comp_apply, hβk]
    exact hqk u
  · intro γ u m hu hm hum
    have key := hβe γ (q' u) m (by trivial) hm hum
    have hqu : q' ⟨((e (π γ) : ↥H) : MulAut V₁) (u : V₁), hu⟩ =
        ⟨((π γ : ↥H') : MulAut Y) ((q' u : ↥(⊤ : Subgroup Y)) : Y), by trivial⟩ :=
      Subtype.ext (heq (π γ) u hu)
    show β' (q' ⟨((e (π γ) : ↥H) : MulAut V₁) (u : V₁), hu⟩) = _
    rw [hqu]
    exact key

theorem n4_d35Five_of_realizes {V₁ Y : Type} [CommGroup V₁] [CommGroup Y] {H : Subgroup (MulAut V₁)}
    {H' : Subgroup (MulAut Y)} {U : Subgroup V₁}
    (hT : ∀ D : FFModel, D.Realizes H' ⊤ (⊤ ⊓ fixV H') → D.Realizes H U (U ⊓ fixV H))
    (h : D35Five H' ⊤) : D35Five H U := by
  rcases h with ⟨n, K, hK, hf, hc, hR⟩ | ⟨n, K, hK, hf, hc, hR⟩ | hR | ⟨K, hK, hf, hc, hR⟩ |
    ⟨K, hK, hf, hc, hR⟩ | ⟨α, hR⟩
  · exact Or.inl ⟨n, K, hK, hf, hc, hT _ hR⟩
  · exact Or.inr (Or.inl ⟨n, K, hK, hf, hc, hT _ hR⟩)
  · exact Or.inr (Or.inr (Or.inl (hT _ hR)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨K, hK, hf, hc, hT _ hR⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨K, hK, hf, hc, hT _ hR⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨α, hT _ hR⟩))))

end Transport

section SecAction

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {VT C V : Subgroup W}

private theorem n4_secHom_mem_stabSub (hLVT : L ≤ stabSub VT) (hLC : L ≤ stabSub C)
    (hLV : ∀ g ∈ L, ∀ v ∈ V, g v ∈ V) (g : ↥L) :
    B5.secHom L hLVT hLC g ∈ stabSub (sec35Img VT C V) := by
  have h : (B5.secHom L hLVT hLC).range ≤ stabSub (sec35Img VT C V) := by
    apply B1.le_stabSub_of_invariant
    rintro _ ⟨g, rfl⟩ x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
    rw [QuotientGroup.mk'_apply, B5.secHom_mk]
    exact Subgroup.mem_map.2 ⟨_, hLV g g.2 (w : W) hw, rfl⟩
  exact h ⟨g, rfl⟩

private noncomputable def n4ResHom (hLVT : L ≤ stabSub VT) (hLC : L ≤ stabSub C)
    (hLV : ∀ g ∈ L, ∀ v ∈ V, g v ∈ V) : ↥L →* MulAut ↥(sec35Img VT C V) :=
  (resHom (sec35Img VT C V)).comp ((B5.secHom L hLVT hLC).codRestrict (stabSub (sec35Img VT C V))
    (n4_secHom_mem_stabSub hLVT hLC hLV))

private theorem n4ResHom_mem (hLVT : L ≤ stabSub VT) (hLC : L ≤ stabSub C)
    (hLV : ∀ g ∈ L, ∀ v ∈ V, g v ∈ V) (g : ↥L) :
    n4ResHom hLVT hLC hLV g ∈ autSub (autSec L VT C) (sec35Img VT C V) := by
  refine mem_autSub.2 ⟨⟨_, n4_secHom_mem_stabSub hLVT hLC hLV g⟩, ?_, rfl⟩
  rw [← B5.range_secHom L hLVT hLC]
  exact ⟨g, rfl⟩

private noncomputable def n4F (hLVT : L ≤ stabSub VT) (hLC : L ≤ stabSub C)
    (hLV : ∀ g ∈ L, ∀ v ∈ V, g v ∈ V) : ↥L →* ↥(autSub (autSec L VT C) (sec35Img VT C V)) :=
  (n4ResHom hLVT hLC hLV).codRestrict _ (n4ResHom_mem hLVT hLC hLV)

private theorem n4F_surjective (hLVT : L ≤ stabSub VT) (hLC : L ≤ stabSub C)
    (hLV : ∀ g ∈ L, ∀ v ∈ V, g v ∈ V) : Function.Surjective (n4F hLVT hLC hLV) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨ψ, hψ, rfl⟩ := mem_autSub.1 hφ
  rw [← B5.range_secHom L hLVT hLC] at hψ
  obtain ⟨g, hg⟩ := hψ
  exact ⟨g, Subtype.ext (congrArg (resHom (sec35Img VT C V)) (Subtype.ext hg))⟩

private noncomputable def n4Q (hVVT : V ≤ VT) : ↥V →* ↥(sec35Img VT C V) :=
  ((QuotientGroup.mk' (C.subgroupOf VT)).comp (Subgroup.inclusion hVVT)).codRestrict _ (fun v =>
    Subgroup.mem_map.2 ⟨Subgroup.inclusion hVVT v, v.2, rfl⟩)

private theorem n4Q_surjective (hVVT : V ≤ VT) : Function.Surjective (n4Q (C := C) hVVT) := by
  rintro ⟨x, hx⟩
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
  exact ⟨⟨(w : W), hw⟩, Subtype.ext rfl⟩

private theorem n4Q_eq_one_iff (hVVT : V ≤ VT) (v : ↥V) :
    n4Q (C := C) hVVT v = 1 ↔ (v : W) ∈ C := by
  rw [← Subtype.coe_inj]
  show (QuotientGroup.mk (Subgroup.inclusion hVVT v) : Sec VT C) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

private theorem n4F_q (hLVT : L ≤ stabSub VT) (hLC : L ≤ stabSub C) (hVVT : V ≤ VT)
    (hLV : ∀ g ∈ L, ∀ v ∈ V, g v ∈ V) (g : ↥L) (v : ↥V) :
    ((n4F hLVT hLC hLV g : ↥(autSub (autSec L VT C) (sec35Img VT C V))) : MulAut ↥(sec35Img VT C V))
        (n4Q hVVT v) = n4Q hVVT ⟨(g : MulAut W) v, hLV g g.2 v v.2⟩ := rfl

private theorem n4F_eq_one_iff (hLVT : L ≤ stabSub VT) (hLC : L ≤ stabSub C) (hVVT : V ≤ VT)
    (hLV : ∀ g ∈ L, ∀ v ∈ V, g v ∈ V) (g : ↥L) :
    n4F hLVT hLC hLV g = 1 ↔ ∀ v ∈ V, (g : MulAut W) v * v⁻¹ ∈ C := by
  constructor
  · intro h v hv
    have h1 := n4F_q hLVT hLC hVVT hLV g ⟨v, hv⟩
    rw [h, OneMemClass.coe_one, MulAut.one_apply] at h1
    have h2 : n4Q (C := C) hVVT (⟨(g : MulAut W) v, hLV g g.2 v hv⟩ * (⟨v, hv⟩ : ↥V)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h1, mul_inv_cancel]
    exact (n4Q_eq_one_iff hVVT _).1 h2
  · intro h
    apply Subtype.ext
    refine MulEquiv.ext fun x => ?_
    obtain ⟨v, rfl⟩ := n4Q_surjective (C := C) hVVT x
    rw [n4F_q hLVT hLC hVVT hLV g v, OneMemClass.coe_one, MulAut.one_apply]
    have h2 := (n4Q_eq_one_iff (C := C) hVVT (⟨(g : MulAut W) v, hLV g g.2 v v.2⟩ * v⁻¹)).2
      (h v v.2)
    rwa [map_mul, map_inv, mul_inv_eq_one] at h2

end SecAction

section Std

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

omit [Finite W] in
private theorem n4_trivial_of_central (hcomm : commSub V L = V) {z : MulAut W}
    (hzL : ∀ l ∈ L, z * l = l * z) (hz : ∀ v ∈ V, z v * v⁻¹ ∈ fixV L) : ∀ v ∈ V, z v = v := by
  have hle : commSub V L ≤ z.toMonoidHom.eqLocus (MonoidHom.id W) := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, w, hw, rfl⟩
    have h1 : z (l w) = l (z w) := by
      have := congrArg (fun φ : MulAut W => φ w) (hzL l hl)
      simpa [MulAut.mul_apply] using this
    have h3 : l (z w * w⁻¹) = z w * w⁻¹ := hz w hw l hl
    have hzw : z w = (z w * w⁻¹) * w := by rw [inv_mul_cancel_right]
    show z (l w * w⁻¹) = l w * w⁻¹
    rw [map_mul, map_inv, h1, hzw, map_mul, h3, ← div_eq_mul_inv, ← div_eq_mul_inv,
      mul_div_mul_left_eq_div, div_eq_mul_inv]
  intro v hv
  rw [← hcomm] at hv
  exact hle hv

private theorem n4_inv (hD : D3Std M Mp T L V) : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V :=
  (mem_irrPlus_top_iff.1 hD.hyp.irr).1

private theorem n4_stab_orbSup (hD : D3Std M Mp T L V) : Mp ≤ stabSub (orbSup T V) := by
  have hT : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
    rw [hD.hyp.Mp_eq]
    exact le_normalizer_conjClosure L T
  refine B1.le_stabSub_of_invariant fun x hx w hw => ?_
  have key : orbSup T V ≤ (orbSup T V).comap x.toMonoidHom := by
    refine orbSup_le fun s hs => ?_
    rintro _ ⟨v, hv, rfl⟩
    show x (s v) ∈ orbSup T V
    have hx' : s⁻¹ * x * s ∈ Mp := (Subgroup.mem_normalizer_iff''.mp (hT hs) x).mp hx
    have h1 : x (s v) = s ((s⁻¹ * x * s) v) := by simp [MulAut.mul_apply]
    rw [h1]
    exact map_le_orbSup hs ⟨_, n4_inv hD _ hx' v hv, rfl⟩
  exact key hw

omit [Finite W] in
private theorem n4_stab_C (T : Subgroup (MulAut W)) (V : Subgroup W) :
    Mp ≤ stabSub (orbSup T V ⊓ fixV Mp) :=
  B1.le_stabSub_of_invariant fun x hx w hw => by
    rw [hw.2 x hx]
    exact hw

private theorem n4F_exists_ne (hD : D3Std M L T L V) :
    ∃ k, n4F (n4_stab_orbSup hD) (n4_stab_C T V) (n4_inv hD) k ≠ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, hcomm, hlt, -⟩ := mem_irrPlus_top_iff.mp hD.hyp.irr
  have h1 : commSub V L ≤ fixV L := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    exact ((n4F_eq_one_iff (n4_stab_orbSup hD) (n4_stab_C T V) (le_orbSup T V) (n4_inv hD)
      ⟨x, hx⟩).1 (hcon ⟨x, hx⟩) w hw).2
  apply hlt.not_ge
  intro v hv
  exact ⟨hv, h1 (hcomm.symm ▸ hv)⟩

private theorem n4_ker (hD : D3Std M L T L V) {g : ↥L}
    (hg : n4F (n4_stab_orbSup hD) (n4_stab_C T V) (n4_inv hD) g = 1) :
    g ∈ Subgroup.center ↥L ∧ ∀ v ∈ V, (g : MulAut W) v = v := by
  have hc : g ∈ Subgroup.center ↥L :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hD.hyp.quasi (n4F_exists_ne hD) hg
  refine ⟨hc, n4_trivial_of_central (mem_irrPlus_top_iff.mp hD.hyp.irr).2.1 ?_ ?_⟩
  · intro l hl
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨l, hl⟩)).symm
  · intro v hv
    exact ((n4F_eq_one_iff (n4_stab_orbSup hD) (n4_stab_C T V) (le_orbSup T V) (n4_inv hD) g).1
      hg v hv).2

private theorem n4_five (hD : D3Std M L T L V)
    (hfix : fixV (autSec L (orbSup T V) (orbSup T V ⊓ fixV L)) = ⊥)
    (hfaith : ∀ g ∈ L, (∀ v ∈ V, g v = v) → g = 1)
    (h5 : D35Five (autSub (autSec L (orbSup T V) (orbSup T V ⊓ fixV L))
        (sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V))
      (⊤ : Subgroup ↥(sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V))) : D35Five L V := by
  have hLVT := n4_stab_orbSup hD
  have hLC : L ≤ stabSub (orbSup T V ⊓ fixV L) := n4_stab_C T V
  have hVVT := le_orbSup T V
  have hLV := n4_inv hD
  have hinj : Function.Injective (n4F hLVT hLC hLV) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hfaith g g.2 (n4_ker hD hg).2)
  let e := MulEquiv.ofBijective (n4F hLVT hLC hLV) ⟨hinj, n4F_surjective hLVT hLC hLV⟩
  refine n4_d35Five_of_realizes (fun D hR => ?_) h5
  obtain ⟨π, hπ⟩ := hR
  refine ⟨e.symm.toMonoidHom.comp π, n4_realizesVia_transport e.symm.toMonoidHom e.symm.surjective
    inf_le_left (fun h u hu => hLV h h.2 u hu)
    (fun h z hz => Subgroup.mem_inf.2 ⟨hLV h h.2 z (Subgroup.mem_inf.1 hz).1, ?_⟩) (n4Q hVVT)
    (n4Q_surjective hVVT) (fun u => ⟨fun hu => ?_, fun hu => ?_⟩) (fun h' u hu => ?_) hπ⟩
  · rw [(Subgroup.mem_inf.1 hz).2 h h.2]
    exact (Subgroup.mem_inf.1 hz).2
  ·
    have hu' := (Subgroup.mem_inf.1 hu).2
    have hmem : ((n4Q hVVT u : ↥(sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V)) :
        Sec (orbSup T V) (orbSup T V ⊓ fixV L)) ∈ fixV (autSec L (orbSup T V) (orbSup T V ⊓ fixV L)) := by
      refine mem_fixV.2 fun ψ hψ => ?_
      rw [← B5.range_secHom L hLVT hLC] at hψ
      obtain ⟨g, rfl⟩ := hψ
      exact congrArg Subtype.val (hu' _ (n4F hLVT hLC hLV g).2)
    rw [hfix, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_inf.2
      ⟨u.2, (Subgroup.mem_inf.1 ((n4Q_eq_one_iff hVVT u).1 (Subtype.ext hmem))).2⟩
  · rw [(n4Q_eq_one_iff hVVT u).2 (Subgroup.mem_inf.2 ⟨hVVT u.2, (Subgroup.mem_inf.1 hu).2⟩)]
    exact one_mem _
  · have h1 : n4F hLVT hLC hLV (e.symm h') = h' := e.apply_symm_apply h'
    have h2 := n4F_q hLVT hLC hVVT hLV (e.symm h') u
    rw [h1] at h2
    exact h2.symm

end Std

section Faithful

variable {W : Type} [CommGroup W] [Finite W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}

private theorem n4_injective_of_faithful {V₁ : Type*} [CommGroup V₁] {D : FFModel} (hD : D.Faithful)
    {H : Subgroup (MulAut V₁)} {U Z : Subgroup V₁} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) : Function.Injective π :=
  CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on hD h

private theorem n4_center_eq_bot_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center G = ⊥) : Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hmem : e.symm z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hz (e g)
  rw [h, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  simpa using congrArg e hmem

private theorem n4_center_ne_top {G : Type*} [Group G] (hG : CFSG.IsQuasisimple G) :
    Subgroup.center G ≠ ⊤ := by
  intro h
  obtain ⟨a, b, hab⟩ := hG.2.2
  apply hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  have hx : x ∈ Subgroup.center G := h ▸ Subgroup.mem_top x
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hx y]

private theorem n4_center_eq_bot_of_simple {G H : Type*} [Group G] [Group H] [IsSimpleGroup G]
    (π : G →* H) (hπ : Function.Surjective π) (hH : CFSG.IsQuasisimple H) :
    Subgroup.center H = ⊥ := by
  have : ((Subgroup.center H).comap π).Normal := Subgroup.Normal.comap inferInstance π
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.center H).comap π) with h | h
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨a, rfl⟩ := hπ z
    have ha : a ∈ (Subgroup.center H).comap π := hz
    rw [h, Subgroup.mem_bot] at ha
    rw [ha, map_one]
    exact Subgroup.one_mem _
  · exfalso
    apply n4_center_ne_top hH
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, rfl⟩ := hπ z
    have ha : a ∈ (Subgroup.center H).comap π := h ▸ Subgroup.mem_top a
    exact ha

private theorem n4_center_statedSp {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Subgroup.center ↥(StatedSp 2 K) = ⊥ := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)
  rw [CFSG.LieType.Universal.Symplectic.center_eq, eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  rw [Subgroup.mem_bot]
  have hmat : (((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K) := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  have hsp : ((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) ∈ TauCeti.GLSymplectic (Fin 2) K := by
    rw [← CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact (g : StatedSp 2 K).2
  rw [TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup, hmat,
    CFSG.ClassicalGroups.Symplectic.scalar_mem_symplecticGroup_iff (by norm_num)] at hsp
  have hc1 : (c : K) = 1 := CharTwo.sq_inj.1 (by rw [hsp, one_pow])
  apply Subtype.ext
  apply Units.ext
  rw [hmat, hc1, map_one]
  rfl

private theorem n4_sqtk (hA21 : AsA21SQTKSection) (hD : D3Std M L T L V) : SQTKGroup ↥L := by
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hD.hyp.qsqtk
  exact B69.sqtk_subgroup hA21 ⟨fun p hp hp2 => hSQT p hp hp2, hK⟩ φ hφ (le_of_mem_cComp hD.hyp.comp)
    hD.hyp.quasi

private theorem n4_odd (hD : D3Std M L T L V) {x : ↥L} (hx : x ∈ Subgroup.center ↥L) :
    Odd (orderOf x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnodd
  obtain ⟨c, hc⟩ := Nat.not_odd_iff_even.mp hnodd
  have hpos : 0 < orderOf x := (isOfFinOrder_of_finite x).orderOf_pos
  have hc0 : 0 < c := by omega
  have hy2 : (x ^ c) ^ 2 = 1 := by
    rw [← pow_mul, show c * 2 = orderOf x by omega, pow_orderOf_eq_one]
  have hne : x ^ c ≠ 1 := fun h => by
    have := Nat.le_of_dvd hc0 (orderOf_dvd_of_pow_eq_one h)
    omega
  have hyc : x ^ c ∈ Subgroup.center ↥L := Subgroup.pow_mem _ hx c
  have hord : orderOf ((x ^ c : ↥L) : MulAut W) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hy2 hne
  have hle : Subgroup.zpowers ((x ^ c : ↥L) : MulAut W) ≤ pCoreOf 2 L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact (x ^ c).2
    · intro l hl
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hcomm : Commute ((x ^ c : ↥L) : MulAut W) l :=
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp hyc ⟨l, hl⟩)).symm
      exact (hcomm.zpow_left k).eq
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  rw [D31.pCoreOf_Mp_eq_bot hD.hyp] at hle
  exact hne (Subtype.ext (Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))))

private theorem n4_inj_of_center (hD : D3Std M L T L V)
    (hc : Subgroup.center ↥(autSub (autSec L (orbSup T V) (orbSup T V ⊓ fixV L))
      (sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V)) = ⊥) :
    Function.Injective (n4F (n4_stab_orbSup hD) (n4_stab_C T V) (n4_inv hD)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hsurj := n4F_surjective (n4_stab_orbSup hD) (n4_stab_C T V) (n4_inv hD)
  have hcen : ∀ z ∈ Subgroup.center ↥L, n4F (n4_stab_orbSup hD) (n4_stab_C T V) (n4_inv hD) z = 1 := by
    intro z hz
    have hmem : n4F (n4_stab_orbSup hD) (n4_stab_C T V) (n4_inv hD) z ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨l, rfl⟩ := hsurj y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hc, Subgroup.mem_bot] at hmem
    exact hmem
  have hgc := (n4_ker hD hg).1
  have hN := hD.hyp.Mp_normal
  have hall : ∀ m ∈ M, ∀ v ∈ V, (g : MulAut W) (m v) = m v := by
    intro m hm v hv
    have hx : m⁻¹ * (g : MulAut W) * m ∈ L := (Subgroup.mem_normalizer_iff''.mp (hN hm) _).mp g.2
    have hxc : (⟨m⁻¹ * (g : MulAut W) * m, hx⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      have hl' : m * (l : MulAut W) * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hN hm) _).mp l.2
      have hcomm := congrArg Subtype.val (Subgroup.mem_center_iff.mp hgc ⟨_, hl'⟩)
      simp only [Subgroup.coe_mul] at hcomm ⊢
      calc (l : MulAut W) * (m⁻¹ * g * m) = m⁻¹ * ((m * l * m⁻¹) * g) * m := by group
        _ = m⁻¹ * (g * (m * l * m⁻¹)) * m := by rw [hcomm]
        _ = m⁻¹ * g * m * l := by group
    have h1 := (n4_ker hD (hcen _ hxc)).2 v hv
    simp only [MulAut.mul_apply] at h1
    calc (g : MulAut W) (m v) = m (m⁻¹ ((g : MulAut W) (m v))) := by simp
      _ = m v := by rw [h1]
  have hgen : (⨆ m ∈ M, V.map m.toMonoidHom) ≤
      (g : MulAut W).toMonoidHom.eqLocus (MonoidHom.id W) := by
    refine iSup₂_le fun m hm => ?_
    rintro _ ⟨v, hv, rfl⟩
    exact hall m hm v hv
  apply Subtype.ext
  ext w
  have hw : w ∈ (⨆ m ∈ M, V.map m.toMonoidHom) := by rw [hD.hyp.gen]; trivial
  exact hgen hw

private theorem n4_injective (hA21 : AsA21SQTKSection) (hNC : AsA36NoOddCover) (hD : D3Std M L T L V)
    (h5 : D35Five (autSub (autSec L (orbSup T V) (orbSup T V ⊓ fixV L))
        (sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V))
      (⊤ : Subgroup ↥(sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V))) :
    Function.Injective (n4F (n4_stab_orbSup hD) (n4_stab_C T V) (n4_inv hD)) := by
  have hsurj := n4F_surjective (n4_stab_orbSup hD) (n4_stab_C T V) (n4_inv hD)
  have hq : CFSG.IsQuasisimple ↥(autSub (autSec L (orbSup T V) (orbSup T V ⊓ fixV L))
      (sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V)) :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hD.hyp.quasi hsurj (n4F_exists_ne hD)
  have hA : IsL345Type ↥(autSub (autSec L (orbSup T V) (orbSup T V ⊓ fixV L))
      (sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V)) →
      Function.Injective (n4F (n4_stab_orbSup hD) (n4_stab_C T V) (n4_inv hD)) := fun hL =>
    hNC _ _ hD.hyp.quasi (n4_sqtk hA21 hD) _ hsurj (fun x hx => n4_odd hD (n4_ker hD hx).1) hL
  rcases h5 with ⟨n, K, _, _, hK, π, hπ⟩ | ⟨n, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ |
    ⟨K, _, _, hK, π, hπ⟩ | ⟨α, π, hπ⟩
  ·
    let e := MulEquiv.ofBijective π ⟨n4_injective_of_faithful (FFModel.nat_faithful _) hπ, hπ.1⟩
    exact hA (Or.inl ⟨n, K, inferInstance, inferInstance, hK, ⟨e.symm⟩⟩)
  ·
    let e := MulEquiv.ofBijective π ⟨n4_injective_of_faithful (FFModel.nat_faithful _) hπ, hπ.1⟩
    exact n4_inj_of_center hD (n4_center_eq_bot_of_equiv e (n4_center_statedSp hK))
  ·
    have : IsSimpleGroup (FFModel.altDn 6).Gam :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact n4_inj_of_center hD (n4_center_eq_bot_of_simple π hπ.1 hq)
  ·
    let e := MulEquiv.ofBijective π ⟨n4_injective_of_faithful (FFModel.nat_faithful _) hπ, hπ.1⟩
    exact hA (Or.inr (Or.inl ⟨K, inferInstance, inferInstance, by simpa using hK, ⟨e.symm⟩⟩))
  ·
    let e := MulEquiv.ofBijective π ⟨n4_injective_of_faithful (FFModel.nat_faithful _) hπ, hπ.1⟩
    exact hA (Or.inr (Or.inr ⟨K, inferInstance, inferInstance, by simpa using hK, ⟨e.symm⟩⟩))
  ·
    have : IsSimpleGroup (FFModel.a7Four α).Gam :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact n4_inj_of_center hD (n4_center_eq_bot_of_simple π hπ.1 hq)

end Faithful

section Main

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem d35_five_of_sec (hD : D3Std M Mp T L V) (hMpL : Mp = L)
    (hfix : fixV (autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp)) = ⊥)
    (hfaith : ∀ g ∈ L, (∀ v ∈ V, g v = v) → g = 1)
    (h5 : D35Five (autSub (autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp))
        (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V))
      (⊤ : Subgroup ↥(sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V))) : D35Five L V := by
  subst hMpL
  exact n4_five hD hfix hfaith h5

theorem d35_faithful (hA21 : AsA21SQTKSection) (hNC : AsA36NoOddCover) (hD : D3Std M Mp T L V)
    (hlt : V < orbSup T V) (hC : ∀ g ∈ Mp, (∀ v ∈ V, g v = v) → ∀ x ∈ Mp, g * x = x * g)
    (hMpL : Mp = L)
    (h5 : D35Five (autSub (autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp))
        (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V))
      (⊤ : Subgroup ↥(sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V))) :
    ∀ g ∈ L, (∀ v ∈ V, g v = v) → g = 1 := by
  have _ := hlt
  have _ := hC
  subst hMpL
  intro g hg hgV
  have h1 : n4F (n4_stab_orbSup hD) (n4_stab_C T V) (n4_inv hD) ⟨g, hg⟩ = 1 :=
    (n4F_eq_one_iff (n4_stab_orbSup hD) (n4_stab_C T V) (le_orbSup T V) (n4_inv hD) ⟨g, hg⟩).2
      fun v hv => by rw [hgV v hv, mul_inv_cancel]; exact one_mem _
  exact congrArg Subtype.val (n4_injective hA21 hNC hD h5 (h1.trans (map_one _).symm))

end Main

end CFSG.Quasithin
