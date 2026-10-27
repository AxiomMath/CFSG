module

public import CFSG.Quasithin.Vol2.Ch10SecB3Aut
public import CFSG.Quasithin.Vol2.Ch10SecBCoordMain
public import CFSG.Quasithin.Vol2.Ch10SecBL32Prod
public import CFSG.Quasithin.Vol2.Ch10SecBPre

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] noncomputable def autCoord {L : Subgroup G} (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ)
    {s : G} (hs : s ∈ Subgroup.normalizer (L : Set G)) : MulAut L32.Γ :=
  ψ.symm.trans ((autQuot2 ↥L (conjAct L ⟨s, hs⟩)).trans ψ)

theorem autCoord_apply {L : Subgroup G} (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ) {s : G}
    (hs : s ∈ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ L) (hx' : s * x * s⁻¹ ∈ L) :
    ψ (mkO2 L (s * x * s⁻¹) hx') = autCoord ψ hs (ψ (mkO2 L x hx)) := by
  simp only [autCoord, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [mkO2, mkO2, autQuot2_mk]
  congr 2

@[expose] def twistSwapAut (α : MulAut L32.Γ) : L32.Γ × L32.Γ →* L32.Γ × L32.Γ :=
  (α.toMonoidHom.comp (MonoidHom.snd _ _)).prod (MonoidHom.fst _ _)

theorem twistSwapAut_apply (α : MulAut L32.Γ) (p : L32.Γ × L32.Γ) :
    twistSwapAut α p = (α p.2, p.1) := rfl

variable [Finite G]

structure L0CoordG (T L : Subgroup G) (t : G) (Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ)
    (α : MulAut L32.Γ) (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ) : Prop where
  surj : Function.Surjective Ψ
  ker : ∀ y : ↥(fsuL0 T L), Ψ y = 1 ↔ (y : G) ∈ pCoreOf 2 (fsuL0 T L)
  hψ : (D1 T L).map ψ.toMonoidHom = L32.U3
  onL : ∀ (l : G) (hl0 : l ∈ fsuL0 T L) (hl : l ∈ L), Ψ ⟨l, hl0⟩ = (ψ (mkO2 L l hl), 1)
  onLt : ∀ (l : G) (hl : l ∈ fsuL0 T L), l ∈ CFSG.conjugate L t → (Ψ ⟨l, hl⟩).1 = 1
  T0 : ((T0 T L).subgroupOf (fsuL0 T L)).map Ψ = L32.U3.prod L32.U3
  swap : ∀ (y : ↥(fsuL0 T L)) (hy : t⁻¹ * y * t ∈ fsuL0 T L),
    Ψ ⟨t⁻¹ * y * t, hy⟩ = (α (Ψ y).2, (Ψ y).1)

theorem exists_L0CoordG
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {T L I : Subgroup G} (hyp : Hyp10 G T L I) (hL32 : LBarL32 L) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ∃ (Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ) (α : MulAut L32.Γ)
      (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ), L0CoordG T L t Ψ α ψ := by
  obtain ⟨φ, hφs, hφk, hφL, hφLt⟩ := SecA.exists_fsuL0_prod h37 h38 hyp ht htn
  obtain ⟨e⟩ := hL32
  obtain ⟨ψ1, hψ1⟩ := exists_equiv_map_eq_U3 e (isSylowTwoOf_D1 hyp)
  let θ := quotO2Equiv (conjEquiv L t)
  let ψ2 := θ.symm.trans ψ1
  let Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ := (ψ1.toMonoidHom.prodMap ψ2.toMonoidHom).comp φ
  have hΨ : ∀ y, Ψ y = (ψ1 (φ y).1, ψ2 (φ y).2) := fun _ => rfl
  have hΨL : ∀ (l : G) (hl : l ∈ L), Ψ ⟨l, SecA.le_fsuL0 T L hl⟩ = (ψ1 (mkO2 L l hl), 1) := by
    intro l hl
    rw [hΨ, hφL l hl]
    simp [ψ2]
  have hΨLt : ∀ (l : G) (hl : l ∈ L) (hl' : t⁻¹ * l * t ∈ fsuL0 T L),
      Ψ ⟨t⁻¹ * l * t, hl'⟩ = (1, ψ1 (mkO2 L l hl)) := by
    intro l hl hl'
    have hm := conj_mem_conjugate' t hl
    have h1 := hφLt _ hm
    rw [hΨ, show (⟨t⁻¹ * l * t, hl'⟩ : ↥(fsuL0 T L)) =
      ⟨t⁻¹ * l * t, SecA.conjugate_le_fsuL0 ht hm⟩ from rfl, h1]
    refine Prod.ext (by simp) ?_
    show ψ1 (θ.symm (mkO2 (CFSG.conjugate L t) _ hm)) = ψ1 (mkO2 L l hl)
    rw [← quotO2Equiv_conjEquiv_mk t hl hm, MulEquiv.symm_apply_apply]
  have hΨc : ∀ (y z : ↥(fsuL0 T L)), (y : G) = z → Ψ y = Ψ z := fun y z h =>
    congrArg Ψ (Subtype.ext h)
  clear_value Ψ
  have hL0eq := SecA.fsuL0_eq_sup h37 h38 hyp ht htn
  have hLle : L ≤ fsuL0 T L := SecA.le_fsuL0 T L
  have hLtle : CFSG.conjugate L t ≤ fsuL0 T L := fun x hx => SecA.conjugate_le_fsuL0 ht hx
  have hTN : ∀ s ∈ T, s ∈ Subgroup.normalizer (fsuL0 T L : Set G) :=
    fun s hs => SecA.le_fsuM T L hs
  have ht2 : t⁻¹ * t⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
    have := Subgroup.inv_mem _ (SecA.mul_self_mem_normalizer h37 h38 hyp ht htn)
    simpa [mul_inv_rev] using this
  have hLt_iff : ∀ {x : G}, x ∈ CFSG.conjugate L t ↔ t * x * t⁻¹ ∈ L := SecA.mem_conjugate_iff
  refine ⟨Ψ, autCoord ψ1 ht2, ψ1, ⟨fun p => ?_, fun y => ?_, hψ1, fun l hl0 hl => ?_,
    fun l hl0 hl => ?_, ?_, ?_⟩⟩
  ·
    obtain ⟨y, hy⟩ := hφs (ψ1.symm p.1, ψ2.symm p.2)
    exact ⟨y, by rw [hΨ, hy]; simp⟩
  ·
    rw [hΨ, Prod.mk_eq_one, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, ← Prod.mk_eq_one,
      Prod.mk.eta, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  ·
    rw [hΨc ⟨l, hl0⟩ ⟨l, hLle hl⟩ rfl, hΨL l hl]
  ·
    have hl' := hLt_iff.mp hl
    have h1 := hΨLt (t * l * t⁻¹) hl' (by simpa [mul_assoc] using hl0)
    rw [hΨc ⟨l, hl0⟩ ⟨t⁻¹ * (t * l * t⁻¹) * t, by simpa [mul_assoc] using hl0⟩ (by group), h1]
  ·
    have hT0L0 : T0 T L ≤ fsuL0 T L := inf_le_right
    have hge : L32.U3.prod L32.U3 ≤ ((T0 T L).subgroupOf (fsuL0 T L)).map Ψ := by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      rw [← hψ1] at ha hb
      obtain ⟨_, ⟨⟨d₁, hd₁L⟩, hd₁, rfl⟩, rfl⟩ := ha
      obtain ⟨_, ⟨⟨d₂, hd₂L⟩, hd₂, rfl⟩, rfl⟩ := hb
      have hd₁T : d₁ ∈ T := (Subgroup.mem_subgroupOf.mp hd₁).1
      have hd₂T : d₂ ∈ T := (Subgroup.mem_subgroupOf.mp hd₂).1
      have hm₂ : t⁻¹ * d₂ * t ∈ fsuL0 T L := hLtle (conj_mem_conjugate' t hd₂L)
      refine ⟨⟨d₁ * (t⁻¹ * d₂ * t), (fsuL0 T L).mul_mem (hLle hd₁L) hm₂⟩,
        Subgroup.mem_subgroupOf.mpr ⟨T.mul_mem hd₁T (T.mul_mem (T.mul_mem (T.inv_mem ht) hd₂T)
          ht), (fsuL0 T L).mul_mem (hLle hd₁L) hm₂⟩, ?_⟩
      rw [show (⟨d₁ * (t⁻¹ * d₂ * t), (fsuL0 T L).mul_mem (hLle hd₁L) hm₂⟩ : ↥(fsuL0 T L)) =
        ⟨d₁, hLle hd₁L⟩ * ⟨t⁻¹ * d₂ * t, hm₂⟩ from rfl, map_mul, hΨL d₁ hd₁L, hΨLt d₂ hd₂L hm₂]
      simp
    have hp : IsPGroup 2 (((T0 T L).subgroupOf (fsuL0 T L)).map Ψ) := by
      have h2 : IsPGroup 2 (T0 T L) := hyp.fsu.sylow.1.to_le inf_le_left
      exact (h2.of_equiv (Subgroup.subgroupOfEquivOfLe hT0L0).symm).map Ψ
    exact eq_U3_prod_of_le hp hge
  ·
    have htN : t⁻¹ ∈ Subgroup.normalizer (fsuL0 T L : Set G) := Subgroup.inv_mem _ (hTN t ht)
    have hfg : Ψ.comp (conjHom (fsuL0 T L) htN) = (twistSwapAut (autCoord ψ1 ht2)).comp Ψ := by
      refine hom_ext_of_sup hLle hLtle hL0eq.symm (fun l hl => ?_) (fun l hl => ?_)
      · have hm : t⁻¹ * l * t ∈ fsuL0 T L := hLtle (conj_mem_conjugate' t hl)
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, twistSwapAut_apply, hΨL l hl,
          hΨc _ ⟨t⁻¹ * l * t, hm⟩ (by rw [conjHom_coe, inv_inv]), hΨLt l hl hm]
        simp
      · have hl' := hLt_iff.mp hl
        have hm2 : t⁻¹ * t⁻¹ * (t * l * t⁻¹) * (t⁻¹ * t⁻¹)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp ht2 _).mp hl'
        have hm : t⁻¹ * (t * l * t⁻¹) * t ∈ fsuL0 T L := by simpa [mul_assoc] using hLtle hl
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, twistSwapAut_apply,
          hΨc _ ⟨_, hLle hm2⟩ (by rw [conjHom_coe]; group), hΨL _ hm2,
          autCoord_apply ψ1 ht2 hl' hm2,
          hΨc ⟨l, hLtle hl⟩ ⟨_, hm⟩ (by group), hΨLt _ hl' hm]
    intro y hy
    have h := congrArg (fun f => f y) hfg
    simp only [MonoidHom.comp_apply, twistSwapAut_apply] at h
    rw [← h]
    exact hΨc _ _ (by rw [conjHom_coe, inv_inv])

omit [Finite G] in
theorem comap_inl_eq_map_fst {B : Subgroup (L32.Γ × L32.Γ)} (hUB : L32.U3.prod L32.U3 ≤ B) :
    B.comap (MonoidHom.inl L32.Γ L32.Γ) = B.map (MonoidHom.fst L32.Γ L32.Γ) := by
  set A : Subgroup L32.Γ := B.map (MonoidHom.fst L32.Γ L32.Γ)
  set N : Subgroup L32.Γ := B.comap (MonoidHom.inl L32.Γ L32.Γ)
  have hUA : L32.U3 ≤ A := fun u hu => ⟨(u, 1), hUB ⟨hu, L32.U3.one_mem⟩, rfl⟩
  have hUN : L32.U3 ≤ N := fun u hu => hUB ⟨hu, L32.U3.one_mem⟩
  have hNA : N ≤ A := fun n hn => ⟨(n, 1), hn, rfl⟩
  have hnorm : ∀ g ∈ A, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    rintro g ⟨p, hp, rfl⟩ n hn
    have h := B.mul_mem (B.mul_mem hp hn) (B.inv_mem hp)
    have heq : p * (n, 1) * p⁻¹ = (p.1 * n * p.1⁻¹, 1) := by ext <;> simp
    show (p.1 * n * p.1⁻¹, (1 : L32.Γ)) ∈ B
    rw [← heq]
    exact h
  rcases L32.overgroups A hUA with h | h | h | h
  · exact le_antisymm hNA (h ▸ hUN)
  · rw [h] at hNA hnorm ⊢; exact L32.eq_pa_of_normal hUN hNA hnorm
  · rw [h] at hNA hnorm ⊢; exact L32.eq_pb_of_normal hUN hNA hnorm
  · rw [h] at hnorm ⊢
    exact L32.eq_top_of_normal hUN fun g n hn => hnorm g (Subgroup.mem_top g) n hn

omit [Finite G] in
theorem eq_prod_of_le {B : Subgroup (L32.Γ × L32.Γ)} (hUB : L32.U3.prod L32.U3 ≤ B) :
    B = (B.map (MonoidHom.fst L32.Γ L32.Γ)).prod (B.map (MonoidHom.snd L32.Γ L32.Γ)) := by
  set σ : L32.Γ × L32.Γ ≃* L32.Γ × L32.Γ := MulEquiv.prodComm
  have hUB' : L32.U3.prod L32.U3 ≤ B.map σ.toMonoidHom := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact ⟨(b, a), hUB ⟨hb, ha⟩, rfl⟩
  have h1 := comap_inl_eq_map_fst hUB
  have h2 := comap_inl_eq_map_fst hUB'
  refine le_antisymm (fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩) ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  have ha' : (a, (1 : L32.Γ)) ∈ B := (h1 ▸ ha : a ∈ B.comap (MonoidHom.inl L32.Γ L32.Γ))
  have hb' : b ∈ (B.map σ.toMonoidHom).map (MonoidHom.fst L32.Γ L32.Γ) := by
    obtain ⟨p, hp, rfl⟩ := hb
    exact ⟨σ p, ⟨p, hp, rfl⟩, rfl⟩
  rw [← h2] at hb'
  obtain ⟨q, hq, hqe⟩ := hb'
  have hq' : q = ((1 : L32.Γ), b) := by
    have := congrArg σ.symm hqe
    simpa [σ] using this
  have := B.mul_mem ha' (hq' ▸ hq)
  simpa using this

omit [Finite G] in
theorem prod_classify_gen {B : Subgroup (L32.Γ × L32.Γ)} {α : MulAut L32.Γ}
    (hUB : L32.U3.prod L32.U3 ≤ B) (hσ : ∀ p ∈ B, (α p.2, p.1) ∈ B) :
    ∃ A : Subgroup L32.Γ, (A = L32.U3 ∨ A = L32.Pa ∨ A = L32.Pb ∨ A = ⊤) ∧ B = A.prod A ∧
      A.map α.toMonoidHom = A := by
  have hB := eq_prod_of_le hUB
  set A₁ := B.map (MonoidHom.fst L32.Γ L32.Γ)
  set A₂ := B.map (MonoidHom.snd L32.Γ L32.Γ)
  have h12 : A₁ ≤ A₂ := by
    intro a ha
    have h1 : (a, (1 : L32.Γ)) ∈ B := by rw [hB]; exact ⟨ha, A₂.one_mem⟩
    exact ⟨_, hσ _ h1, rfl⟩
  have h21 : A₂.map α.toMonoidHom ≤ A₁ := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : ((1 : L32.Γ), b) ∈ B := by rw [hB]; exact ⟨A₁.one_mem, hb⟩
    exact ⟨_, hσ _ h1, rfl⟩
  have hc : Nat.card (A₂.map α.toMonoidHom) = Nat.card A₂ :=
    (Nat.card_congr (A₂.equivMapOfInjective _ α.injective).toEquiv).symm
  have hcard : Nat.card A₂ ≤ Nat.card A₁ := hc ▸ Subgroup.card_le_of_le h21
  have hA : A₁ = A₂ := Subgroup.eq_of_le_of_card_ge h12 hcard
  have hUA : L32.U3 ≤ A₁ := fun u hu => ⟨(u, 1), hUB ⟨hu, L32.U3.one_mem⟩, rfl⟩
  refine ⟨A₁, L32.overgroups A₁ hUA, by rw [hB, ← hA], ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (hA ▸ h21) ?_
  rw [← hA] at hc
  rw [hc]

theorem classify_preIn_gen {T L : Subgroup G} {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ}
    {α : MulAut L32.Γ} {ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ} (hT : quasithinIsSylowTwo T)
    (hC : L0CoordG T L t Ψ α ψ) {Y : Subgroup G} (hT0Y : T0 T L ≤ Y) (hYL0 : Y ≤ fsuL0 T L)
    (htY : ∀ y ∈ Y, t⁻¹ * y * t ∈ Y) :
    ∃ A : Subgroup L32.Γ, (A = L32.U3 ∨ A = L32.Pa ∨ A = L32.Pb ∨ A = ⊤) ∧
      Y = preIn Ψ (A.prod A) ∧ A.map α.toMonoidHom = A := by
  have hUB : L32.U3.prod L32.U3 ≤ imgIn Ψ Y := by
    rw [← hC.T0]
    exact imgIn_mono Ψ hT0Y
  have hσ : ∀ p ∈ imgIn Ψ Y, (α p.2, p.1) ∈ imgIn Ψ Y := by
    intro p hp
    obtain ⟨y, hyL0, hyY, rfl⟩ := mem_imgIn.mp hp
    have hm : t⁻¹ * y * t ∈ fsuL0 T L := hYL0 (htY y hyY)
    exact mem_imgIn.mpr ⟨_, hm, htY y hyY, hC.swap ⟨y, hyL0⟩ hm⟩
  obtain ⟨A, hA, hB, hαA⟩ := prod_classify_gen hUB hσ
  refine ⟨A, hA, ?_, hαA⟩
  rw [← hB]
  exact (preIn_imgIn hYL0 fun x hx =>
    hT0Y (SecA.pCoreOf_fsuL0_le_T0 hT ((hC.ker x).mp hx))).symm

theorem T0_eq_preIn_gen {T L : Subgroup G} {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ}
    {α : MulAut L32.Γ} {ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* L32.Γ} (hT : quasithinIsSylowTwo T)
    (hC : L0CoordG T L t Ψ α ψ) : T0 T L = preIn Ψ (L32.U3.prod L32.U3) := by
  rw [← hC.T0]
  exact (preIn_imgIn inf_le_right fun x hx =>
    SecA.pCoreOf_fsuL0_le_T0 hT ((hC.ker x).mp hx)).symm

end CFSG.Quasithin.Vol2.Ch10.SecB
