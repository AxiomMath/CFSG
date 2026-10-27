
module

public import Certificates.Kernel.Co2I301.SixProof
public import Certificates.Kernel.Co2I301.QChk
public import Certificates.Kernel.SporSch.Co2M.Class
public import Certificates.Kernel.SporSch.Co2M.Span
public import CFSG.Sporadic.Co2I301.SpecAux
public import CFSG.Sporadic.Co2I301.SpecSixAuxBase
public import CFSG.Sporadic.Co2Schreier.Cores

public section

namespace CertificateChecks.KernelCo2I301

open CFSG.KC.Enum CFSG.KC.Co2I301 CFSG.KS CFSG.KS.Co2I301 CFSG.KS.MatRep CFSG.KS.Co2M
  CFSG.Sporadic.Co2I301 CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSporSch.Co2M (PV V_get V_size isInvA_rep vok qrecs qgens QR)

section Q

theorem q_cent : ∀ y ∈ locQ, Commute y (permOfArr 2300 (i301D ())) → y = 1 ∨ y = locZ := by
  intro y hy hc
  obtain ⟨k, hk, rfl⟩ := enumQ_facts.exists_elt repTuple_q hy
  by_cases h0 : k = 0
  · left
    rw [h0]
    exact enumQ_facts.elt_zero
  by_cases h23 : k = 23
  · right
    rw [h23]
    exact eltE_Q_z
  exfalso
  have hck := allN_spec qnc_ok k hk
  rw [beq_false h0, beq_false h23] at hck
  have hf := CFSG.KS.Co2LE.leftEnum_facts vok qrecs qgens (le_refl 512)
  obtain ⟨E', hE⟩ := hf.2.2 k hk
  have he : enumQ.elems[k]! = (CFSG.KS.Co2LE.LL co2PackedVecs QR 512)[k]! := by
    rw [enumQ, hf.1]
  rw [← he] at hE
  have hD : Rep 22 co2PackedVecs (i301D ()) (M 1) (MI 1) := rep_arr 1 (by norm_num)
  have rY : CFSG.Monster.B.Co2.Rep 2300 enumQ.elems[k]! (eltE enumQ k) := enumQ_facts.rep hk
  have rD : CFSG.Monster.B.Co2.Rep 2300 (i301D ()) (permOfArr 2300 (i301D ())) :=
    (rep_permOfArr (isInvA_rep hD)).1
  have e0 : (compA 2300 enumQ.elems[k]! (i301D ()))[0]! =
      (compA 2300 (i301D ()) enumQ.elems[k]!)[0]! := by
    rw [rep_compA rY rD ⟨0, by norm_num⟩, rep_compA rD rY ⟨0, by norm_num⟩, hc.eq]
  rw [compA_get (by norm_num), compA_get (by norm_num)] at e0
  have h0V : 0 < co2PackedVecs.size := by rw [V_size]; norm_num
  obtain ⟨d0l, d0v⟩ := get_rep hD h0V
  obtain ⟨y0l, y0v⟩ := get_rep hE h0V
  obtain ⟨-, a1⟩ := get_rep hE d0l
  obtain ⟨-, a2⟩ := get_rep hD y0l
  have hv := congrArg (fun i => co2PackedVecs[i]!) e0
  rw [a1, a2, d0v, y0v, V_get (by norm_num), ← vmK_eq, ← vmK_eq, ← vmK_eq, ← vmK_eq] at hv
  rw [hv, Nat.beq_refl] at hck
  exact Bool.noConfusion hck

end Q

section Cent

variable [Fact (smallCheck () = true)]

@[expose] noncomputable def phi : locC →* Equiv.Perm (Fin 63) := toPerm63.comp sixAction

theorem phi_mem (c : locC) : phi c ∈ G6 := by
  have h : sixAction c ∈ sixAction.range := ⟨c, rfl⟩
  rw [sixAction_range] at h
  have h2 := Subgroup.mem_map_of_mem toPerm63 h
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  exact ⟨i, hi, (toPerm63_sixAction_cGen hi).symm⟩

theorem gens_C : permOfArr 2300 (i301D ()) ∈ locC ∧ permOfArr 2300 (i301S ()) ∈ locC ∧
    permOfArr 2300 (i301B2 ()) ∈ locC ∧ permOfArr 2300 (i301B3 ()) ∈ locC ∧
    permOfArr 2300 (i301K1 ()) ∈ locC ∧ permOfArr 2300 (i301K2 ()) ∈ locC :=
  SpecAux.gens_mem_locC rfl rfl rfl rfl rfl rfl

theorem comm_C : Commute (permOfArr 2300 (i301D ())) (permOfArr 2300 (i301S ())) ∧
    Commute (permOfArr 2300 (i301D ())) (permOfArr 2300 (i301B2 ())) ∧
    Commute (permOfArr 2300 (i301D ())) (permOfArr 2300 (i301B3 ())) ∧
    Commute (permOfArr 2300 (i301D ())) (permOfArr 2300 (i301K1 ())) ∧
    Commute (permOfArr 2300 (i301D ())) (permOfArr 2300 (i301K2 ())) ∧
    Commute (permOfArr 2300 (i301B2 ())) (permOfArr 2300 (i301B3 ())) ∧
    Commute locZ (permOfArr 2300 (i301D ())) ∧ Commute locZ (permOfArr 2300 (i301S ())) ∧
    Commute locZ (permOfArr 2300 (i301B2 ())) ∧ Commute locZ (permOfArr 2300 (i301B3 ())) ∧
    Commute locZ (permOfArr 2300 (i301K1 ())) ∧ Commute locZ (permOfArr 2300 (i301K2 ())) :=
  SpecAux.commute_facts rfl rfl rfl rfl rfl rfl

@[expose] noncomputable def cD : locC := ⟨permOfArr 2300 (i301D ()), gens_C.1⟩

@[expose] noncomputable def cS : locC := ⟨permOfArr 2300 (i301S ()), gens_C.2.1⟩

@[expose] noncomputable def cK1 : locC := ⟨permOfArr 2300 (i301K1 ()), gens_C.2.2.2.2.1⟩

@[expose] noncomputable def cK2 : locC := ⟨permOfArr 2300 (i301K2 ()), gens_C.2.2.2.2.2⟩

omit [Fact (smallCheck () = true)]
  in
theorem r7_phi {c : locC} {k : ℕ} (hk : k < 10) (hc : (c : Equiv.Perm (Fin 2300)) =
    permOfArr 2300 (i301Arr k)) (hok : sixColsOK (i301Arr k) = true) {F : ℕ}
    (hF : perm63Of (i301Arr k) = CFSG.KS.Raw.unpack 63 7 F) : R7 F (phi c) := by
  have hr : CFSG.Monster.B.Co2.Rep 2300 (i301Arr k) (c : Equiv.Perm (Fin 2300)) := by
    rw [hc]
    exact (rep_permOfArr (isInvA_rep (rep_arr k hk))).1
  have h := rep_perm63Of c hr hok
  rw [hF] at h
  exact CFSG.KS.Raw.Orb.prep_of_rep h

theorem r7_cD : R7 SX.fd (phi cD) :=
  r7_phi (k := 1) (by norm_num) rfl sixColsOK_arr.1 perm63Of_eq.1

theorem r7_cS : R7 SX.fs (phi cS) :=
  r7_phi (k := 2) (by norm_num) rfl sixColsOK_arr.2.1 perm63Of_eq.2.1

theorem r7_cK1 : R7 SX.fk1 (phi cK1) :=
  r7_phi (k := 5) (by norm_num) (by change permOfArr 2300 (i301K1 ()) = _; rw [i301K1_eq])
    sixColsOK_arr.2.2.1 perm63Of_eq.2.2.1

theorem r7_cK2 : R7 SX.fk2 (phi cK2) :=
  r7_phi (k := 6) (by norm_num) (by change permOfArr 2300 (i301K2 ()) = _; rw [i301K2_eq])
    sixColsOK_arr.2.2.2 perm63Of_eq.2.2.2

@[expose] noncomputable def cK (g : ℕ) : locC := if g = 0 then cK1 else cK2

theorem r7_FK {g : ℕ} (hg : g < 2) : R7 (FK g) (phi (cK g)) := by
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · exact r7_cK1
  · exact r7_cK2

local notation "K0P" => Subgroup.closure {permOfArr 2300 (i301K1 ()), permOfArr 2300 (i301K2 ())}

theorem cK_mem {g : ℕ} (hg : g < 2) : ((cK g : locC) : Equiv.Perm (Fin 2300)) ∈ K0P := by
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem fld_one_lt (r o : ℕ) : fld(r, o, 1) < 2 := by
  have := Nat.and_le_right (n := Nat.shiftRight r o) (m := 1)
  change Nat.shiftRight r o &&& 1 < 2
  omega

local notation "X" => phi cD

theorem orbit_mem : ∀ j < 672, ∃ h ∈ G6, R7 (cd (OR j)) (h * X * h⁻¹) :=
  dep_ind (fun j => oDep (OR j)) (fun j => oPar (OR j))
    (fun j => ∃ h ∈ G6, R7 (cd (OR j)) (h * X * h⁻¹))
    (fun j hj e => ⟨1, Subgroup.one_mem _, by
      rw [(oRec_spec (allN_spec o_ok j hj)).1 e, one_mul, inv_one, mul_one]
      exact r7_cD⟩)
    fun j hj e => by
      obtain ⟨hp, hd, hc⟩ := (oRec_spec (allN_spec o_ok j hj)).2.1 e
      have hl : oLet (OR j) < 2 := fld_one_lt _ _
      refine ⟨hp, hd, fun ⟨h, hh, hr⟩ => ⟨sixPi (oLet (OR j)) * h,
        Subgroup.mul_mem _ (sixPi_mem hl) hh, ?_⟩⟩
      rw [hc]
      have e' : sixPi (oLet (OR j)) * h * X * (sixPi (oLet (OR j)) * h)⁻¹ =
          sixPi (oLet (OR j)) * (h * X * h⁻¹) * (sixPi (oLet (OR j)))⁻¹ := by group
      rw [e']
      exact r7_cj (r7_PI hl) (r7_PII hl) hr

theorem card_C : Nat.card ↥(G6 ⊓ Subgroup.centralizer {X}) ≤ 2160 := by
  choose! h hhG hh using orbit_mem
  have hinc : ∀ j < 672, incr OR 672 j = true := fun j hj => (oRec_spec (allN_spec o_ok j hj)).2.2
  have key := card_cent_le (G := G6) (x := X) (N := 672) (fun j => h j * X * (h j)⁻¹)
    (fun j hj => ⟨h j, hhG j hj, rfl⟩)
    (fun i hi j hj e => incr_perm_inj hinc hi hj (hh i hi) (e ▸ hh j hj))
  rw [card_G6] at key
  omega

theorem k_mem : ∀ j < 360, ∃ k : locC, (k : Equiv.Perm (Fin 2300)) ∈ K0P ∧ R7 (cd (KR j)) (phi k) :=
  dep_ind (fun j => kDep (KR j)) (fun j => kPar (KR j))
    (fun j => ∃ k : locC, (k : Equiv.Perm (Fin 2300)) ∈ K0P ∧ R7 (cd (KR j)) (phi k))
    (fun j hj e => ⟨1, Subgroup.one_mem _, by
      rw [(kRec_spec (allN_spec k_ok j hj)).1 e, map_one]
      exact r7_idc⟩)
    fun j hj e => by
      obtain ⟨hp, hd, hc⟩ := (kRec_spec (allN_spec k_ok j hj)).2 e
      have hl : kLet (KR j) < 2 := fld_one_lt _ _
      refine ⟨hp, hd, fun ⟨k, hk, hr⟩ => ⟨k * cK (kLet (KR j)),
        Subgroup.mul_mem _ hk (cK_mem hl), ?_⟩⟩
      rw [hc, map_mul]
      exact r7_cp hr (r7_FK hl)

@[expose] noncomputable def au (u : ℕ) : locC := cD ^ (u % 3) * cS ^ (u / 3)

theorem r7_AU (u : ℕ) : R7 (AU u) (phi (au u)) := by
  rw [au, map_mul, map_pow, map_pow]
  exact r7_cp (r7_pw r7_cD _) (r7_pw r7_cS _)

theorem l_mem : ∀ i < 2160, ∃ k : locC, (k : Equiv.Perm (Fin 2300)) ∈ K0P ∧
    ∃ u < 6, R7 (cd (LR i)) (phi (k * au u)) := by
  intro i hi
  obtain ⟨hk, hu, hc, -, -⟩ := lRec_spec (allN_spec l_ok i hi)
  obtain ⟨k, hkK, hr⟩ := k_mem _ hk
  refine ⟨k, hkK, _, hu, ?_⟩
  rw [hc, map_mul]
  exact r7_cp hr (r7_AU _)

theorem commute_D_of_K0 {k : Equiv.Perm (Fin 2300)} (hk : k ∈ K0P) :
    Commute k (permOfArr 2300 (i301D ())) := by
  have hle : K0P ≤ Subgroup.centralizer {permOfArr 2300 (i301D ())} := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 comm_C.2.2.2.1.eq.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 comm_C.2.2.2.2.1.eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hk))

theorem commute_cD {c : locC} (h : Commute (c : Equiv.Perm (Fin 2300)) (cD : Equiv.Perm _)) :
    Commute c cD := Subtype.ext h.eq

theorem au_comm (u : ℕ) : Commute (au u) cD := by
  have hs : Commute cS cD := commute_cD comm_C.1.symm
  exact ((Commute.refl cD).pow_left _).mul_left (hs.pow_left _)

theorem exists_L : ∀ c ∈ G6 ⊓ Subgroup.centralizer {X}, ∃ i < 2160, ∃ k : locC,
    (k : Equiv.Perm (Fin 2300)) ∈ K0P ∧ ∃ u < 6, R7 (cd (LR i)) (phi (k * au u)) ∧
      phi (k * au u) = c := by
  choose! kk hkK uu hu hr using l_mem
  have hinc : ∀ j < 2160, incr LR 2160 j = true :=
    fun j hj => (lRec_spec (allN_spec l_ok j hj)).2.2.2.1
  intro c hc
  obtain ⟨i, hi, e⟩ := exists_of_card_le (H := G6 ⊓ Subgroup.centralizer {X}) (M := 2160)
    (fun i => phi (kk i * au (uu i)))
    (fun i hi => ⟨phi_mem _, Subgroup.mem_centralizer_singleton_iff.2 (by
      have hcomm : Commute (kk i * au (uu i)) cD :=
        (commute_cD (commute_D_of_K0 (hkK i hi))).mul_left (au_comm _)
      exact (hcomm.map phi).eq)⟩)
    (fun i hi j hj e => incr_perm_inj hinc hi hj (hr i hi) (e ▸ hr j hj)) card_C c hc
  exact ⟨i, hi, kk i, hkK i hi, uu i, hu i hi, hr i hi, e⟩

theorem ker_cent {y : locC} (hy : phi y = 1) (hyd : Commute (y : Equiv.Perm (Fin 2300))
    (permOfArr 2300 (i301D ()))) : (y : Equiv.Perm (Fin 2300)) = 1 ∨
      (y : Equiv.Perm (Fin 2300)) = locZ := by
  have h1 : sixAction y = 1 := toPerm63_injective (by rw [map_one]; exact hy)
  have h2 : y ∈ sixAction.ker := h1
  rw [sixAction_ker, Subgroup.mem_subgroupOf] at h2
  exact q_cent _ h2 hyd

theorem cent_facts : RowCentFacts := by
  intro g hg hgd hgz
  have hgC : g ∈ locC := by
    rw [locC_eq_centralizer]
    exact ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 hgz.eq⟩
  set gc : locC := ⟨g, hgC⟩
  have hgcD : Commute gc cD := commute_cD hgd
  have hpx : phi gc ∈ G6 ⊓ Subgroup.centralizer {X} :=
    ⟨phi_mem gc, Subgroup.mem_centralizer_singleton_iff.2 (hgcD.map phi).eq⟩
  obtain ⟨i, hi, k, hkK, u, hu, hr, e⟩ := exists_L _ hpx
  have hy1 : phi ((k * au u)⁻¹ * gc) = 1 := by rw [map_mul, map_inv, e, inv_mul_cancel]
  have hka : Commute (k * au u) cD := (commute_cD (commute_D_of_K0 hkK)).mul_left (au_comm _)
  have hyD : Commute (((k * au u)⁻¹ * gc : locC) : Equiv.Perm (Fin 2300))
      (permOfArr 2300 (i301D ())) := by
    have := hka.inv_left.mul_left hgcD
    exact congrArg Subtype.val this.eq
  have hgeq : g = (k : Equiv.Perm (Fin 2300)) * (au u : Equiv.Perm (Fin 2300)) *
      (((k * au u)⁻¹ * gc : locC) : Equiv.Perm (Fin 2300)) := by
    have e : gc = k * au u * ((k * au u)⁻¹ * gc) := by group
    exact congrArg Subtype.val e
  have hzS : Commute locZ (permOfArr 2300 (i301S ())) := comm_C.2.2.2.2.2.2.2.1
  have hauE : ∀ u, (au u : Equiv.Perm (Fin 2300)) =
      permOfArr 2300 (i301D ()) ^ (u % 3) * permOfArr 2300 (i301S ()) ^ (u / 3) := fun u => by
    rw [au, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
    rfl
  refine ⟨?_, fun h1 h2 => ?_⟩
  ·
    rcases ker_cent hy1 hyD with hy | hy
    · refine ⟨u % 3, 0, u / 3, by omega, by norm_num, by omega, ?_⟩
      rw [hgeq, hy, hauE, pow_zero, mul_one, mul_one, mul_inv_cancel_right]
      exact hkK
    · refine ⟨u % 3, 1, u / 3, by omega, by norm_num, by omega, ?_⟩
      rw [hgeq, hy, hauE, pow_one]
      have hc : permOfArr 2300 (i301S ()) ^ (u / 3) * locZ =
          locZ * permOfArr 2300 (i301S ()) ^ (u / 3) := ((hzS.pow_right (u / 3)).eq).symm
      have e1 : (k : Equiv.Perm (Fin 2300)) *
          (permOfArr 2300 (i301D ()) ^ (u % 3) * permOfArr 2300 (i301S ()) ^ (u / 3)) * locZ *
          (permOfArr 2300 (i301D ()) ^ (u % 3) * locZ * permOfArr 2300 (i301S ()) ^ (u / 3))⁻¹ =
          k := by
        calc (k : Equiv.Perm (Fin 2300)) *
              (permOfArr 2300 (i301D ()) ^ (u % 3) * permOfArr 2300 (i301S ()) ^ (u / 3)) * locZ *
              (permOfArr 2300 (i301D ()) ^ (u % 3) * locZ * permOfArr 2300 (i301S ()) ^ (u / 3))⁻¹
            = (k : Equiv.Perm (Fin 2300)) * permOfArr 2300 (i301D ()) ^ (u % 3) *
              (permOfArr 2300 (i301S ()) ^ (u / 3) * locZ) *
              (permOfArr 2300 (i301D ()) ^ (u % 3) * locZ * permOfArr 2300 (i301S ()) ^ (u / 3))⁻¹ :=
              by group
          _ = (k : Equiv.Perm (Fin 2300)) * permOfArr 2300 (i301D ()) ^ (u % 3) *
              (locZ * permOfArr 2300 (i301S ()) ^ (u / 3)) *
              (permOfArr 2300 (i301D ()) ^ (u % 3) * locZ * permOfArr 2300 (i301S ()) ^ (u / 3))⁻¹ :=
              by rw [hc]
          _ = k := by group
      rw [e1]
      exact hkK
  ·
    have hk1 : Commute gc cK1 := Subtype.ext h1.eq
    have hk2 : Commute gc cK2 := Subtype.ext h2.eq
    have hz : R7 (cd (LR i)) (phi gc) := by rw [← e]; exact hr
    have cm1 : cm (cd (LR i)) SX.fk1 = true := by
      unfold cm
      have hq : R7 (cp SX.fk1 (cd (LR i))) (phi gc * phi cK1) := by
        rw [(hk1.map phi).eq]
        exact r7_cp r7_cK1 hz
      rw [eq_of_r7 (cp_shr _ _) (cp_shr _ _) (r7_cp hz r7_cK1) hq]
      exact Nat.beq_refl _
    have cm2 : cm (cd (LR i)) SX.fk2 = true := by
      unfold cm
      have hq : R7 (cp SX.fk2 (cd (LR i))) (phi gc * phi cK2) := by
        rw [(hk2.map phi).eq]
        exact r7_cp r7_cK2 hz
      rw [eq_of_r7 (cp_shr _ _) (cp_shr _ _) (r7_cp hz r7_cK2) hq]
      exact Nat.beq_refl _
    obtain ⟨u', hu', hcu⟩ : ∃ u' < 3, cd (LR i) = AU u' := by
      rcases (lRec_spec (allN_spec l_ok i hi)).2.2.2.2 cm1 cm2 with h | h | h
      exacts [⟨0, by norm_num, h⟩, ⟨1, by norm_num, h⟩, ⟨2, by norm_num, h⟩]
    have hphi : phi gc = phi (au u') := r7_unique hz (by rw [hcu]; exact r7_AU u')
    have hy1' : phi ((au u')⁻¹ * gc) = 1 := by rw [map_mul, map_inv, hphi, inv_mul_cancel]
    have hyD' : Commute ((((au u')⁻¹ * gc : locC)) : Equiv.Perm (Fin 2300))
        (permOfArr 2300 (i301D ())) := by
      have := (au_comm u').inv_left.mul_left hgcD
      exact congrArg Subtype.val this.eq
    have hgeq' : g = (au u' : Equiv.Perm (Fin 2300)) *
        (((au u')⁻¹ * gc : locC) : Equiv.Perm (Fin 2300)) := by
      have e : gc = au u' * ((au u')⁻¹ * gc) := by group
      exact congrArg Subtype.val e
    have hau' : (au u' : Equiv.Perm (Fin 2300)) = permOfArr 2300 (i301D ()) ^ u' := by
      rw [hauE, Nat.mod_eq_of_lt hu', Nat.div_eq_of_lt hu', pow_zero, mul_one]
    rcases ker_cent hy1' hyD' with hy | hy
    · exact ⟨u', 0, hu', by norm_num, by rw [hgeq', hy, hau', pow_zero, mul_one]⟩
    · exact ⟨u', 1, hu', by norm_num, by rw [hgeq', hy, hau', pow_one]⟩

end Cent

end CertificateChecks.KernelCo2I301

end
