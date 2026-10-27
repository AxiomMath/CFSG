module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CZM
public import CFSG.Quasithin.Vol2.Ch10SecQ3CZO

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem eq_or_eq_of_conj (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {X : Subgroup G} (hX : X = L ∨ X = CFSG.conjugate L t) {m : G} (hm : m ∈ fsuM T L) :
    X.map (MulAut.conj m).toMonoidHom = L ∨
      X.map (MulAut.conj m).toMonoidHom = CFSG.conjugate L t := by
  have hloc := hyp.fsu.maximal.1
  have hXc : X ∈ cComp (fsuM T L) := by
    rcases hX with h | h <;> rw [h]
    · exact SecA.mem_cComp_fsuM hloc
    · exact SecA.conjugate_mem_cComp_fsuM hloc (SecA.le_fsuM T L ht)
  have hXL0 : X ≤ fsuL0 T L := by
    rcases hX with h | h <;> rw [h]
    · exact SecA.le_fsuL0 T L
    · exact SecA.conjugate_le_fsuL0 ht
  have hYc := H13.LocDbl.map_conj_mem_cComp hXc (Subgroup.le_normalizer hm)
  have hYL0 : X.map (MulAut.conj m).toMonoidHom ≤ fsuL0 T L := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hm x).mp (hXL0 hx)
  exact SecE.eq_or_eq_of_mem_cComp_L0T h37 h38 hyp ht htn
    (cComp_mem_of_le hYc (hYL0.trans le_sup_left)
      (sup_le (SecA.fsuL0_le_fsuM T L) (fun x hx => SecA.le_fsuM T L hx)))

theorem not_le_normalizer_of_sylow (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {X : Subgroup G}
    (hX : X = L ∨ X = CFSG.conjugate L t) {N : Subgroup G} (hN : IsSylowTwoOf N (fsuM T L)) :
    ¬ N ≤ Subgroup.normalizer (X : Set G) := by
  intro hNX
  have hT : IsSylowTwoOf T (fsuM T L) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow (SecA.le_fsuM T L)
  obtain ⟨h, hhM, hh⟩ := A4.exists_conj_of_isSylowTwoOf hN hT
  have hTY : T ≤ Subgroup.normalizer ((X.map (MulAut.conj h).toMonoidHom : Subgroup G) :
      Set G) := fun x hx => mem_normalizer_map_conj (hNX ((hh x).mp hx))
  rcases eq_or_eq_of_conj h37 h38 hyp ht htn hX hhM with hY | hY <;>
    rw [hY] at hTY
  · exact hyp.not_normal hTY
  · apply hyp.not_normal
    intro x hx
    have h1 := hTY (T.mul_mem (T.mul_mem (T.inv_mem ht) hx) ht)
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro y
    have h2 := h1 (t⁻¹ * y * t)
    rw [SecA.mem_conjugate_iff, SecA.mem_conjugate_iff] at h2
    simpa [mul_assoc] using h2

omit [Finite G] in
theorem two_dvd_relIndex_pCoreOf {X : Subgroup G} {n : ℕ} (hX : IsLin2Type X n) (hn : 1 ≤ n) :
    2 ∣ (pCoreOf 2 X).relIndex X := by
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := hX
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have h1 : (pCoreOf 2 X).subgroupOf X = CFSG.pCore 2 ↥X := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    exact C10P34.mem_pCoreOf_iff x.2
  rw [Subgroup.relIndex, h1, ← hαk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hαs,
    Subgroup.card_top, SecA.card_SL_two_pow hF']
  exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _

variable {H K : Subgroup G} {n k : ℕ} {b : G}
  {hel : IsElemAbelian 2 (VZ T H)} {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
  {K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))}
  {c : Ctx T L I H K n k b hel I' K₀} {t : G} {L₁ : Subgroup G}

abbrev sOne (T : Subgroup G) (b : G) : Subgroup G := ⁅baum T, Subgroup.zpowers b⁆

abbrev bOne (L₁ T : Subgroup G) (b : G) : Subgroup G :=
  L₁ ⊓ Subgroup.normalizer (sOne T b : Set G)

abbrev mOne (L₁ T : Subgroup G) (b : G) : Subgroup G :=
  Subgroup.normalizer (sOne T b : Set G) ⊓ Subgroup.normalizer (bOne L₁ T b : Set G)

omit [Finite G] in
theorem centralizer_le_normalizer_of_le {X Y : Subgroup G} (h : X ≤ Y) :
    Subgroup.centralizer (Y : Set G) ≤ Subgroup.normalizer (X : Set G) :=
  (Subgroup.centralizer_le h).trans (Subgroup.centralizer_le_normalizer _)

theorem Ctx.sOne_le_baum (c : Ctx T L I H K n k b hel I' K₀) : sOne T b ≤ baum T := by
  rw [Subgroup.commutator_le]
  intro s hs x hx
  rw [commutatorElement_def]
  have hxN : x ∈ Subgroup.normalizer (baum T : Set G) := Subgroup.zpowers_le.mpr c.hbS hx
  have e : s * x * s⁻¹ * x⁻¹ = s * (x * s⁻¹ * x⁻¹) := by group
  rw [e]
  exact (baum T).mul_mem hs ((Subgroup.mem_normalizer_iff.mp hxN _).mp ((baum T).inv_mem hs))

theorem Ctx.b_mem_normalizer_sOne (c : Ctx T L I H K n k b hel I' K₀) :
    b ∈ Subgroup.normalizer (sOne T b : Set G) :=
  SecA.le_normalizer_commutator (Subgroup.zpowers_le.mpr c.hbS) Subgroup.le_normalizer
    (Subgroup.mem_zpowers b)

namespace Ctx9

variable (d : Ctx9 c t L₁)
include d

theorem S₁_eq : sOne T b = T ⊓ L₁ := by
  have hle : sOne T b ≤ T ⊓ L₁ := le_inf (c.sOne_le_baum.trans (B2F.baum_le T)) d.hS₁L₁.1
  exact le_antisymm hle ((A4.isSylowTwoOf_iff_maximal.mp d.hS₁L₁).2.2 _ inf_le_right
    (c.hyp.fsu.sylow.1.to_le inf_le_left) hle)

theorem T1_le_normalizer_L₁ : T1 T L ≤ Subgroup.normalizer (L₁ : Set G) := by
  rcases d.hL₁ with h | h <;> rw [h]
  · exact inf_le_right
  · exact SecB.T1_le_normalizer_conjugate c.h37 c.h38 c.hyp d.ht

theorem T1_le_normalizer_L₂ : T1 T L ≤
    Subgroup.normalizer ((L₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  intro s hs
  refine mem_normalizer_map_conj (d.T1_le_normalizer_L₁ ?_)
  have h := (Subgroup.mem_normalizer_iff.mp (SecB.T1_normal c.h37 c.h38 c.hyp
    (T.inv_mem d.ht)) s).mp hs
  simpa using h

theorem T1_le_normalizer_S₁ : T1 T L ≤ Subgroup.normalizer (sOne T b : Set G) := by
  rw [d.S₁_eq]
  intro s hs
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hs.1, d.T1_le_normalizer_L₁ hs⟩

theorem B₁_eq : bOne L₁ T b = sOne T b ⊔ Subgroup.zpowers b :=
  inf_normalizer_eq_sup d.hL₁blk.2.1 d.hS₁L₁ d.hbL₁ c.b_mem_normalizer_sOne c.orderOf_b

theorem B₁_le_K : bOne L₁ T b ≤ K := by
  rw [d.B₁_eq]
  exact sup_le d.hS₁K.1 (Subgroup.zpowers_le.mpr c.hbK)

theorem T1_le_M₁ : T1 T L ≤ mOne L₁ T b := fun _ hs =>
  ⟨d.T1_le_normalizer_S₁ hs, Subgroup.inf_normalizer_le_normalizer_inf
    ⟨d.T1_le_normalizer_L₁ hs, Subgroup.le_normalizer (d.T1_le_normalizer_S₁ hs)⟩⟩

theorem L₂_le_centralizer :
    L₁.map (MulAut.conj t).toMonoidHom ≤ Subgroup.centralizer (L₁ : Set G) := by
  have h := d.commutator_L
  rw [Subgroup.commutator_comm] at h
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

theorem K₂_le_centralizer :
    K.map (MulAut.conj t).toMonoidHom ≤ Subgroup.centralizer (K : Set G) := by
  have h := d.commutator_K
  rw [Subgroup.commutator_comm] at h
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

theorem L₂_le_M₁ :
    L₁.map (MulAut.conj t).toMonoidHom ≤ mOne L₁ T b := fun _ hy =>
  ⟨centralizer_le_normalizer_of_le d.hS₁L₁.1 (d.L₂_le_centralizer hy),
    centralizer_le_normalizer_of_le inf_le_left (d.L₂_le_centralizer hy)⟩

theorem K₂_le_M₁ :
    K.map (MulAut.conj t).toMonoidHom ≤ mOne L₁ T b := fun _ hy =>
  ⟨centralizer_le_normalizer_of_le d.hS₁K.1 (d.K₂_le_centralizer hy),
    centralizer_le_normalizer_of_le d.B₁_le_K (d.K₂_le_centralizer hy)⟩

omit [Finite G] d in
theorem B₁_le_M₁ : bOne L₁ T b ≤ mOne L₁ T b := fun _ hx => ⟨hx.2, Subgroup.le_normalizer hx⟩

theorem S₁_ne_bot : sOne T b ≠ ⊥ := by
  intro h
  have hU : blockU L₁ ≤ sOne T b :=
    (d.hL₁blk.1.2.2.1.1.trans inf_le_left).trans (B6.pCoreOf_two_le_of_isSylowTwoOf d.hS₁L₁)
  rw [h, le_bot_iff] at hU
  have h1 := d.hL₁blk.1.2.2.2.2.1
  rw [hU] at h1
  exact not_lt_bot h1

theorem pCoreOf_M₁_ne_bot : pCoreOf 2 (mOne L₁ T b) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁M : sOne T b ≤ mOne L₁ T b := fun x hx =>
    B₁_le_M₁ ⟨d.hS₁L₁.1 hx, Subgroup.le_normalizer hx⟩
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hS₁M inf_le_left
    d.hS₁L₁.2.1
  intro h
  rw [h, le_bot_iff] at hle
  exact d.S₁_ne_bot hle

end Ctx9

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
