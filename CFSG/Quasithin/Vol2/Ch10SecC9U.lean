module

public import CFSG.Quasithin.Vol2.Ch10SecC10
public import CFSG.Quasithin.Vol2.Ch10SecC8X

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_isU (hyp : Hyp10 G T L I) {K : Subgroup G}
    (hKV : ⁅fsuVM T L I, K⁆ ≤ fsuVM T L I) : ∃ U : Subgroup G, IsU10_2_8 T L I K U := by
  have hTN : ∀ s ∈ T1 T L, ∀ v ∈ fsuVM T L I, s * v * s⁻¹ ∈ fsuVM T L I := fun s hs v hv =>
    (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_fsuVM T L I hs.1) v).mp hv
  let U : Subgroup G :=
    { carrier := {v | v ∈ ⁅fsuVM T L I, K⁆ ∧ ∀ s ∈ T1 T L, s * v * s⁻¹ * v⁻¹ ∈ fsuCVM T L I}
      one_mem' := ⟨Subgroup.one_mem _, fun s _ => by
        rw [mul_one, mul_inv_cancel, inv_one, mul_one]
        exact Subgroup.one_mem _⟩
      mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, fun s hs => by
        have haV := hKV ha.1
        have hc := hb.2 s hs
        have e : s * (a * b) * s⁻¹ * (a * b)⁻¹ =
            (s * a * s⁻¹ * a⁻¹) * (a * (s * b * s⁻¹ * b⁻¹) * a⁻¹) := by group
        have e2 : a * (s * b * s⁻¹ * b⁻¹) * a⁻¹ = s * b * s⁻¹ * b⁻¹ := by
          rw [fsuVM_comm hyp haV hc.1, mul_inv_cancel_right]
        rw [e, e2]
        exact Subgroup.mul_mem _ (ha.2 s hs) hc⟩
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, fun s hs => by
        have haV := hKV ha.1
        have hc := Subgroup.inv_mem _ (ha.2 s hs)
        have e : s * a⁻¹ * s⁻¹ * a⁻¹⁻¹ = a⁻¹ * (s * a * s⁻¹ * a⁻¹)⁻¹ * a := by group
        have e2 : a⁻¹ * (s * a * s⁻¹ * a⁻¹)⁻¹ * a = (s * a * s⁻¹ * a⁻¹)⁻¹ := by
          rw [mul_assoc, fsuVM_comm hyp hc.1 haV, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [e, e2]
        exact hc⟩ }
  exact ⟨U, fun v hv => hv.1, fun v hv => ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩⟩

omit [Finite G] in
theorem exists_isR (K U : Subgroup G) : ∃ R : Subgroup G, IsR10_2_8 T L I K U R := by
  set P := pCoreOf 2 (autOn (centralizerSection K U (fsuCVM T L I)) (fsuVM T L I))
  refine ⟨T ⊓ (P.comap (conjAct (fsuVM T L I))).map
      (Subgroup.normalizer (fsuVM T L I : Set G)).subtype, inf_le_left, fun x hx => ⟨?_, ?_⟩⟩
  · rintro ⟨-, ⟨y, hy, rfl⟩⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hxN, hxP⟩
    exact ⟨hx, ⟨x, hxN⟩, hxP, rfl⟩

theorem mem_fsuM_of_conjugate_le
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1013 : Stmt10_1_3) (h1026 : Stmt10_2_6) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {x : G}
    (hx2 : x ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hxL0 : x ∉ Subgroup.centralizer (fsuL0 T L : Set G)) {g : G}
    (hLgx : CFSG.conjugate L g ≤ Subgroup.centralizer ({x} : Set G))
    (hLgM : CFSG.conjugate L g ≤ fsuM T L) : g ∈ fsuM T L := by
  have hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    SecA.isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.faithful hyp.not_normal
  have hloc := hyp.fsu.maximal.1
  have hn := SecA.fsuL0_le_normalizer hloc
  have hnt := SecA.fsuL0_le_normalizer_conjugate hloc (SecA.le_fsuM T L ht)
  have hL0 := SecA.fsuL0_eq_sup h37 h38 hyp ht htn
  obtain ⟨hVM, hR, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, -, hV2L, -⟩ := hdec t ht htn
  have hLperf : ⁅L, L⁆ = L := commutator_self_of_local hyp.fsu.faithful.1
  have hLtL0 : CFSG.conjugate L t ≤ fsuL0 T L := SecA.conjugate_le_fsuL0 ht
  have hV2V : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer (hLtL0.trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  obtain ⟨p, hp, hp2, hpd⟩ :=
    exists_odd_prime_dvd_card hsimp (nonabelian_of_isQuasisimple hyp.fsu.quasisimple)
  have hM : oPrimeResidualOf p (fsuM T L) = fsuL0 T L := h1013 G T L I hyp p hp hp2 hpd
  have hLp : oPrimeResidualOf p L = L := oPrimeResidualOf_eq_self hp hLperf hsimp hpd
  have hLgL0 : CFSG.conjugate L g ≤ fsuL0 T L := by
    have hLgp : oPrimeResidualOf p (CFSG.conjugate L g) = CFSG.conjugate L g := by
      rw [SecA.conjugate_eq_map, oPrimeResidualOf_map, hLp]
    rw [← hLgp, ← hM]
    exact oPrimeResidualOf_mono p hLgM
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := mem_centralizer_iff_le.mp (hV2L hx2)
  have hxLt : x ∉ Subgroup.centralizer (CFSG.conjugate L t : Set G) := fun h =>
    hxL0 (hL0 ▸ mem_centralizer_sup (hV2L hx2) h)
  have hOA : pCoreOf 2 (CFSG.conjugate L t) ≤ Subgroup.centralizer (fsuVM T L I : Set G) :=
    pCoreOf_le_centralizer_of_subnormal hR hVM (subnormal_of_le_normalizer hLtL0 hnt)
  have hLgL : CFSG.conjugate L g ≤ L :=
    le_of_le_fsuL0_of_le_centralizer hLperf hsimp hL0 hn hnt ⟨t, rfl⟩ ⟨g, rfl⟩ hOA (hV2V hx2)
      hLx hxLt hLgL0 hLgx
  have heq : CFSG.conjugate L g = L :=
    Subgroup.eq_of_le_of_card_ge hLgL (card_conjugate L g).ge
  exact (h1026 G T L I hyp).2.2 (SecA.conjugate_eq_self_iff.mp heq)

omit [Finite G] in
theorem conjugate_le_centralizer_of_mem_normalizer {Y : Subgroup G} {g : G}
    (hLY : L ≤ Subgroup.centralizer (Y : Set G)) (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    CFSG.conjugate L g ≤ Subgroup.centralizer (Y : Set G) := by
  intro z hz
  rw [SecA.mem_conjugate_iff] at hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hgy : g * y * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  have hc := Subgroup.mem_centralizer_iff.mp (hLY hz) _ hgy
  calc y * z = g⁻¹ * ((g * y * g⁻¹) * (g * z * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * z * g⁻¹) * (g * y * g⁻¹)) * g := by rw [hc]
    _ = z * y := by group

theorem normalizer_le_of_centralizer_le
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1013 : Stmt10_1_3) (h1026 : Stmt10_2_6) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {x : G}
    (hx2 : x ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hxL0 : x ∉ Subgroup.centralizer (fsuL0 T L : Set G)) {Y : Subgroup G} (hxY : x ∈ Y)
    (hLY : L ≤ Subgroup.centralizer (Y : Set G))
    (hCY : Subgroup.centralizer (Y : Set G) ≤ fsuM T L) :
    Subgroup.normalizer (Y : Set G) ≤ fsuM T L := by
  intro g hg
  have h1 := conjugate_le_centralizer_of_mem_normalizer hLY hg
  refine mem_fsuM_of_conjugate_le h37 h38 hyp h1011 h1013 h1026 ht htn hx2 hxL0
    (h1.trans (Subgroup.centralizer_le (by simpa using hxY))) (h1.trans hCY)

theorem le_fsuM_of_le (hyp : Hyp10 G T L I) (h1026 : Stmt10_2_6) {H : Subgroup G}
    (hH : fsuL0 T L ⊔ T1 T L ≤ H) (hO : pCoreOf 2 H ≠ ⊥) : H ≤ fsuM T L := by
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have hU := (h1026 G T L I hyp).1
  have h1 : M' = fsuM T L := hU.2 M' ⟨hM'.1, hH.trans hM'.2⟩
  exact h1 ▸ hM'.2

theorem centralizer_le_of_isUniqueM (hyp : Hyp10 G T L I) (h1026 : Stmt10_2_6) {X : Subgroup G}
    (hX : IsPGroup 2 X) (hX1 : X ≠ ⊥) (hXab : X ≤ Subgroup.centralizer (X : Set G))
    (hXc : fsuL0 T L ⊔ T1 T L ≤ Subgroup.centralizer (X : Set G)) :
    Subgroup.centralizer (X : Set G) ≤ fsuM T L := by
  refine le_fsuM_of_le hyp h1026 hXc fun h => hX1 (le_bot_iff.mp ?_)
  rw [← h]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) hXab
    (Subgroup.centralizer_le_normalizer _) hX

end CFSG.Quasithin.Vol2.Ch10.SecC
