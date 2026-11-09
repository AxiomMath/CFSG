module

public import CFSG.Certificates.Kernel.GHarrisFus.Sound

public section

set_option maxRecDepth 400000

namespace CFSG.KC.GHFus

open CFSG.ComponentClassification.GHarris.SCert

@[expose] noncomputable def mulS (x y : Nat) : Nat :=
  64 * dmN (x / 64) (y / 64) + addS (x % 64) (mvN (x / 64) (y % 64))

@[expose] noncomputable def invT : Nat := nat_lit 11480655697544365381246244717580261747170059228572682760534074048413148862883505720748254608388383933906480782576595112585743790978017236925821247672623793469275251681973716993261235248609050763064218526140436156619109371022224788542494137857111005212876102254837301971387584280429275348195841178619636768323891395874039427983302899943528604245157133101664190682484932736380896785382727624803242726199803066068245674333839749841995039938725663712969792529182001273633638341923056362709120553209591347448352717025951522170451137912673809294283916887997797703079042401101294488405185222951365122807838382193436452697574867524911267202733737672869745275180900740699995574591819409194362904368631878483864338241480609257862079166396175812499477109668084843290419658979301962339299350758821067164650595559983858908797799421637969797951169676955190491665263790623036796964653795173037052492992953346819193357541110339456967087579060965246544151657978929855671512316520135794323147483654728842866936843192526426611379247121381522215268642578140708428592648199116735713027180812075519478758575128212596271811222707823224866775433093120474506867541441855007205831854520149568251177963994036893288517656939495376133375290493341748879533487422162310834961279522961832660089038748539920558738999860788936978364694176019525325386243609769526382571683731002457770788368144609234103070506055202912077312

@[expose] noncomputable def invK (c : Nat) : Nat :=
  Nat.land (Nat.shiftRight invT (Nat.mul (nat_lit 9) c)) (nat_lit 511)

theorem invT_ok : allBelow 512 (fun c => Nat.blt (invK c) 512 && Nat.beq (mulS (invK c) c) 0) =
    true := by
  decide +kernel

theorem enc_dec (c : Nat) : (SE.dec c).enc = c % 512 := by
  simp only [SE.enc, SE.dec, Fin.val_ofNat, ZMod.val_natCast]
  omega

theorem se_eq_iff (a b : SE) : a = b ↔ a.enc = b.enc := ⟨fun h => h ▸ rfl, enc_inj⟩

theorem enc_mulS (a b : SE) : (a * b).enc = mulS a.enc b.enc := (mulS_enc a b).symm

theorem enc_one : (1 : SE).enc = 0 := rfl

theorem enc_inv (a : SE) : (a⁻¹).enc = invK a.enc := by
  have h := allBelow_spec invT_ok a.enc (SE.enc_lt a)
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hlt, h1⟩ := h
  have hb : (SE.dec (invK a.enc)).enc = invK a.enc := by rw [enc_dec, Nat.mod_eq_of_lt hlt]
  have hm : SE.dec (invK a.enc) * a = 1 := by
    rw [se_eq_iff, enc_mulS, hb, enc_one]
    exact Nat.eq_of_beq_eq_true h1
  rw [← eq_inv_of_mul_eq_one_left hm, hb]

theorem forall_se {P : SE → Prop} : (∀ s, P s) ↔ ∀ c, c < 512 → P (SE.dec c) :=
  ⟨fun h c _ => h _, fun h s => SE.dec_enc s ▸ h _ (SE.enc_lt s)⟩

theorem exists_se {P : SE → Prop} : (∃ s, P s) ↔ ∃ c, c < 512 ∧ P (SE.dec c) :=
  ⟨fun ⟨s, hs⟩ => ⟨s.enc, SE.enc_lt s, (SE.dec_enc s).symm ▸ hs⟩, fun ⟨_, _, h⟩ => ⟨_, h⟩⟩

theorem predE_iff (s : SE) : SE.predE s ↔ predEK s.enc = true := by
  rw [predEK_enc, decide_eq_true_iff]

theorem predF_iff (s : SE) : SE.predF s ↔ predFK s.enc = true := by
  rw [predFK_enc, decide_eq_true_iff]

@[expose] noncomputable def invRepT : Nat := nat_lit 1475816936174686111797280

theorem enc_invRep (i : Fin 9) :
    (SE.invRep i).enc = Nat.land (Nat.shiftRight invRepT (Nat.mul 9 i.val)) 511 := by
  revert i
  decide +kernel

theorem enc_gen0 : (SE.gen 0).enc = 32 := by decide +kernel

end CFSG.KC.GHFus
